import Veil
set_option linter.dupNamespace false



veil module DAG

type address
instantiate inst: LE address
instantiate decLE: DecidableRel inst.le
instantiate ord : Ord address
type nodeSet
instantiate nset: ByzNodeSet address nodeSet

type block
abbrev round := Nat
abbrev wave := Fin 6
instantiate instw: LE wave
instantiate decLEw: DecidableRel instw.le
instantiate ordw: Ord wave

type vtxs

@[veil_decl]
structure vertex (address block: Type) where
  source: address
  payload: block
deriving instance Veil.Enumeration for vertex
deriving instance Veil.FinEncodableInjOnly for vertex
instantiate instv: LE $ vertex address block
instantiate decLEv: DecidableRel $ instv.le
instantiate ordv: Ord $ vertex address block


-- we need to quantify over vertices,
-- so the round parameter is separated from the vertex type
instantiate vset: TSet (vertex address block) vtxs

@[veil_decl]
structure message (address block vtxs: Type) where
  payload: vertex address block
  strong: vtxs
  weak: vtxs
deriving instance Veil.Enumeration for message
deriving instance Veil.FinEncodableInjOnly for message
-- set_option trace.Meta.synthInstance true in

@[veil_decl]
structure edge (address block: Type) where
  top: vertex address block
  bot: vertex address block
deriving instance Veil.Enumeration for edge

@[veil_decl]
structure Graph (vtxs edge: Type) where
  nodes: vtxs
  strong: List edge
  weak: List edge

immutable individual replicas: List address

function view
  : address
  → Graph vtxs (edge address block)
function current_round
  : address
  → round

immutable function a_bcast: address → round → block
function r_bcast
  : address
  → message address block vtxs
  → Option round
function r_deliver
  : address
  → message address block vtxs
  → address
  → Option round
relation chooseLeader: address → wave → Bool
function waveLeader: wave → Option address
function decidedWave: address → wave
relation a_deliver_at: address → block → round → address → wave → Bool

function recvLog: address → (checked: vertex address block) → Option (round × (message address block vtxs))
-- when receiving, set the `recvLog` of the vertex from the r_deliver
relation voted: address → vertex address block → Bool
function waveVertexLeader: address → wave → Option (vertex address block)
immutable individual f: Nat
#gen_state

after_init {
  current_round I := 0
  view I := Graph.mk vset.empty [] []

  r_bcast I M := none
  r_deliver I M J := none

  chooseLeader I W := false
  waveLeader W := none
  decidedWave I := (0: Fin 6)

  a_deliver_at I B R A W := false

  recvLog I V := none
  voted I V := false

  waveVertexLeader I W := none
}

action DAG_maintain (i: address) {
  let g := view i
  let v
   :| recvLog i v ≠ none
    ∧ ¬ vset.contains v g.nodes
  require recvLog i v ≠ none
  require ¬ vset.contains v g.nodes
  let mut ret := g
  if let some (r, m) := recvLog i v then
    if (
      let timecheck := (r ≤ current_round i)
      let deps := vset.union m.strong m.weak |> vset.toList
      let depscheck :=
        ∀ v': vertex address block
        , v' ∈ deps
        → vset.contains v' g.nodes
      let majority_escape := r == 1
      let majority :=
        (m.strong |> vset.count) > 2 * f + 1
      let validity :=
        ∀ v': vertex address block
        , v' ∈ m.strong
        → (recvLog i v')
          <&> ( fun (r', _) => r' + 1 == r
          ) = some true
      ; timecheck
      ∧ (majority_escape ∨ majority)
      ∧ validity
      ∧ depscheck
    )
    then
      let strong_edges
        := vset.toList m.strong |> List.map (fun v' => edge.mk v v')
      let weak_edges
        := vset.toList m.weak |> List.map (fun v' => edge.mk v v')
      ret := Graph.mk
        (vset.insert v g.nodes)
        (strong_edges ++ g.strong)
        (weak_edges ++ g.weak)
  view i := ret
}

-- action ReliableBroadcast (i: address) (j: address) {
--   let m :| r_bcast i m ≠ none ∧ r_deliver j m i = none
--   r_deliver j m i := r_bcast i m
-- }

action GlobalPerfectCoin (w: wave) {
  if
      waveLeader w = none
    ∧ ∃ s: nodeSet
      , nset.supermajority s
      ∧ ∀ i: address, nset.member i s → chooseLeader i w
    then
  -- let wl :| wl ∈ replicas
      let wl <- pick address
      waveLeader w := some wl
}

action ChooseLeader (i: address) (w: wave) {
  require current_round i > 4 * (w-1)
  chooseLeader i w := true
  GlobalPerfectCoin w
}

-- action recv (i: address) (m: message address block vtxs) {
--   let j :| r_deliver i m j ≠ none
--   require vset.count m.strong > (2 * f + 1)
--     ∨ (r_deliver i m j <&> (·==1)) == some true
--   let checked := vertex.mk j m.payload.payload
--   recvLog i checked := (r_deliver i m j).map (·, m)
--   DAG_maintain i
-- }

-- action send (i: address) {
--   let r := current_round i
--   let b := a_bcast i r
--   let v := vertex.mk i b
--   let g := view i
--   require
--     ∀ m: message address block vtxs
--     , r_bcast i m ≠ none
--     → r_bcast i m ≠ some r
--   require r ≠ 0
--   require r = 1 ∨
--     ∃ s: nodeSet
--     , nset.supermajority s
--     ∧ ∀ i: address
--       , nset.member i s
--       → ∃ v': vertex address block
--         , vset.contains v' g.nodes
--         ∧ (·.1 == r-1) <$> recvLog i v' = some true
--   let m
--    := message.mk v
--     (vset.filter g.nodes
--       (fun v' => ((·.1 == r-1) <$> recvLog i v') = some true))
--     (vset.filter g.nodes
--       (fun v' => (((fun (r', _) => decide $ r' < r-1) <$> recvLog i v') = some true) ∧ voted i v' = false))
--   r_bcast i m := some r
--   voted i V := vset.contains V g.nodes
--   let strong_edges
--     := vset.toList m.strong |> List.map (fun v' => edge.mk v v')
--   let weak_edges
--     := vset.toList m.weak |> List.map (fun v' => edge.mk v v')
--   view i := Graph.mk
--     (vset.insert v g.nodes)
--     (strong_edges ++ g.strong)
--     (weak_edges ++ g.weak)
--   recvLog i v := some (r, m)
-- }

action getWaveVertexLeader (i: address) (w: wave) {
  require w > 0
  require current_round i > 4 * (w-1)
  ChooseLeader i w
  let g := view i
  let mut ret := waveVertexLeader i w
  if ret ≠ none then return ()
  if let some j := waveLeader w then
    let v
      :| vset.contains v g.nodes
      && recvLog i v <&> (·.1 = 4 * (w-1) + 1) == some true
      && v.source == j
    ret := v
  waveVertexLeader i w := ret
}

-- ghost relation strong_path (i: address) (top bot: vertex address block) :=
--   let g := view i
--   let topr := recvLog i top
--   let botr := recvLog i bot
--   ∃ (s: vtxs)
--   , ( ∀ v: vertex address block
--       , vset.contains v s
--       → vset.contains v g.nodes
--       ∧ let r := recvLog i v
--         ( v = top ∨ v = bot
--         ∨ ( (fun (topr, _) (botr, _) (r, _) => botr < r ∧ r < topr)
--             <$> topr <*> botr <*> r == some true
--         ))
--     )
--   ∧ ( ∀ v1 v2: vertex address block
--       , vset.contains v1 s
--       ∧ vset.contains v2 s
--       → v1 = v2
--       ∨ let r1 := recvLog i v1
--         let r2 := recvLog i v2
--         (·.1 ≠ ·.1) <$> r1 <*> r2 == some true
--     )
--   ∧ ( ∀ v: vertex address block
--       , vset.contains v s
--       → v = top
--       ∨ ∃ v': vertex address block
--         , { top := v', bot := v } ∈ g.strong
--     )

-- ghost relation path (i: address) (top: vertex address block) (bot: vertex address block) :=
--   let g := view i
--   let topr := recvLog i top
--   let botr := recvLog i bot
--   ∃ (s: vtxs)
--   , ( ∀ v: vertex address block
--       , vset.contains v s
--       → vset.contains v g.nodes
--       ∧ ( v = top ∨ v = bot
--         ∨ (do
--             let (r, _) <- recvLog i v
--             let (topr', _) <- topr
--             let (botr', _) <- botr
--             pure $ decide $ botr' < r ∧ r < topr'
--           ).getD false
--         )
--     )
--   ∧ ( ∀ v1 v2: vertex address block
--       , vset.contains v1 s
--       ∧ vset.contains v2 s
--       → v1 = v2
--       ∨ (do
--           let r1 <- recvLog i v1
--           let r2 <- recvLog i v2
--           pure $ decide $ r1 ≠ r2
--         ).getD false
--     )
--   ∧ ( ∀ v: vertex address block
--       , vset.contains v s
--       → v = top
--       ∨ ∃ v': vertex address block
--         , { top := v', bot := v } ∈ g.strong ∪ g.weak
--     )


-- action waveReady (i: address) (w: wave) {
--   let vo <- getWaveVertexLeader i w
--   let wd := decidedWave i
--   let mut leaderStack: List $ vertex address block := []
--   let sliceRound := (4: Nat) * w
--   -- let prepare := (do
--   --   let v_ <- vo
--   --   pure $
--   --     ∃ (s: vtxs)
--   --       , vset.count s > 2 * f + 1
--   --       ∧ ∀ (v: vertex address block)
--   --         , vset.contains v s
--   --         → (do
--   --             let (r, _) <- recvLog i v
--   --             pure $ r = sliceRound
--   --               ∧ strong_path i v v_
--   --           ).getD False
--   -- ).getD False
--   -- if ¬ prepare then return ()
--   -- if let some v_ := vo then
--   --   let mut v := v_
--   --   for w' in List.range (w-1 - wd) |> List.map (fun index => w-1-index ) do
--   --     let v' <- getWaveVertexLeader i w'
--   --     if let some v_ := v' then
-- }

-- action advanceRound (i: address) {
--   return ()
-- }

-- action test_for {
--   let mut l: List Nat := []
--   for i in ([1,2,3]: List Nat) do
--     l := l.insert i
-- }
#gen_spec

end DAG

#check Veil.VeilM.pickSuchThat
