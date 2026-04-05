import Veil
set_option linter.dupNamespace false



veil module DAG

type address
-- instantiate inst: LE address
-- instantiate decLE: DecidableRel inst.le
-- instantiate ord : Ord address
type nodeSet
instantiate nset: ByzNodeSet address nodeSet

type block
abbrev round := Nat
abbrev wave := Fin 3
instantiate instw: LE wave
instantiate decLEw: DecidableRel instw.le
instantiate ordw: Ord wave

-- type vtxs

@[veil_decl]
structure vertex (address block: Type) where
  source: address
  payload: block
deriving instance Veil.Enumeration for vertex
deriving instance Veil.FinEncodableInjOnly for vertex
-- instantiate instv: LE $ vertex address block
-- instantiate decLEv: DecidableRel $ instv.le
-- instantiate ordv: Ord $ vertex address block
-- set_option trace.Meta.synthInstance true in
-- deriving instance DecidableEq for vertex

-- we need to quantify over vertices,
-- so the round parameter is separated from the vertex type
-- instantiate vset: TSet (vertex address block) vtxs

@[veil_decl]
structure message (address block : Type) where
  payload: vertex address block
  strong: List $ vertex address block
  weak: List $ vertex address block
-- deriving instance Veil.Enumeration for message
-- deriving instance Veil.FinEncodableInjOnly for message

@[veil_decl]
structure edge (address block: Type) where
  top: vertex address block
  bot: vertex address block
deriving instance Veil.Enumeration for edge

@[veil_decl]
structure Graph (address block edge: Type) where
  nodes: List $ vertex address block
  strong: List edge
  weak: List edge

function view
  : address
  → Graph address block (edge address block)
function current_round
  : address
  → round

immutable function a_bcast: address → round → block
-- function r_bcast
--   : address
--   → message address block
--   → Option round
function r_bcast: address → List (message address block × round)
-- function r_deliver
--   : address
--   → message address block
--   → address
--   → Option round
function r_deliver: address → List (message address block × address × round)
-- relation chooseLeader: address → wave → Bool
function chooseLeader: address → List wave
function waveLeader: wave → Option address
function decidedWave: address → wave
-- relation a_deliver_at: address → block → round → address → wave → Bool
function a_deliver_at: address → List (block × round × address × wave)

-- function recvLog: address → (checked: vertex address block) → Option (round × (message address block vtxs))
function recvLog: address → List ((vertex address block × round × message address block))
-- when receiving, set the `recvLog` of the vertex from the r_deliver
function voted: address → List (vertex address block)
function waveVertexLeader: address → wave → Option (vertex address block)
immutable individual f: Nat

individual test_: Nat
#gen_state

after_init {
  current_round I := 0
  view I := Graph.mk [] [] []

  r_bcast I := []
  r_deliver I := []

  -- chooseLeader I W := false
  chooseLeader I := []
  waveLeader W := none
  decidedWave I := (0: wave)

  -- a_deliver_at I B R A W := false
  a_deliver_at I := []

  -- recvLog I V := none
  recvLog I := []
  voted I := []

  waveVertexLeader I W := none
}

action DAG_maintain (i: address) {
  let g := view i
  -- let v
  --  :| recvLog i v ≠ none
  --   ∧ ¬ vset.contains v g.nodes
  let recv := (recvLog i).mergeSort (fun (_, r, _) (_, r', _) => r < r')
  view i := recv.foldl (fun ga (v, r, msg) =>
  if (
    let timecheck := (r ≤ current_round i)
    let deps := msg.strong ++ msg.weak
    let depscheck := deps.all (fun v => v ∈ g.nodes)
    let majority_escape := r == 1
    let majority := msg.strong.length > 2 * f + 1
    let validity := (do
      let v' <- msg.strong
      let (c', r', _) <- recvLog i
      -- guard (v' == c')
      if v' ≠ c' then [] else
      pure $ r' + 1 == r
    ).all (·)
      ; timecheck
    && (majority_escape || majority)
    && validity
    && depscheck
  ) then
    let strong_edges := msg.strong.map (edge.mk v)
    let weak_edges := msg.weak.map (edge.mk v)
    Graph.mk
      (g.nodes.insert v)
      (strong_edges ++ g.strong)
      (weak_edges ++ g.weak)
    else ga ) g
  -- require recvLog i v ≠ none
  -- require ¬ vset.contains v g.nodes
  -- let mut ret := g
  -- if let some (r, m) := recvLog i v then
  --   if (
  --     let timecheck := (r ≤ current_round i)
  --     let deps := vset.union m.strong m.weak |> vset.toList
  --     let depscheck :=
  --       ∀ v': vertex address block
  --       , v' ∈ deps
  --       → vset.contains v' g.nodes
  --     let majority_escape := r == 1
  --     let majority :=
  --       (m.strong |> vset.count) > 2 * f + 1
  --     let validity :=
  --       ∀ v': vertex address block
  --       , v' ∈ m.strong
  --       → (recvLog i v')
  --         <&> ( fun (r', _) => r' + 1 == r
  --         ) = some true
  --     ; timecheck
  --     ∧ (majority_escape ∨ majority)
  --     ∧ validity
  --     ∧ depscheck
  --   )
  --   then
  --     let strong_edges
  --       := vset.toList m.strong |> List.map (fun v' => edge.mk v v')
  --     let weak_edges
  --       := vset.toList m.weak |> List.map (fun v' => edge.mk v v')
  --     ret := Graph.mk
  --       (vset.insert v g.nodes)
  --       (strong_edges ++ g.strong)
  --       (weak_edges ++ g.weak)
  -- view i := ret
}

action ReliableBroadcast (i: address) (j: address) {
  -- let m :| r_bcast i m ≠ none ∧ r_deliver j m i = none
  let mpack :| mpack ∈ r_bcast i
  let (m, r) := mpack
  if (m, i, r) ∈ r_deliver j then return ()
  -- r_deliver j m i := r_bcast i m
  r_deliver j := r_deliver j |> List.insert (m, i, r)
}

action GlobalPerfectCoin (w: wave) {
  if
      waveLeader w = none
    ∧ ∃ s: nodeSet
      , nset.supermajority s
      ∧ ∀ i: address
        , nset.member i s
        → w ∈ chooseLeader i
    then
  -- let wl :| wl ∈ replicas
      let wl <- pick address
      waveLeader w := some wl
}

action ChooseLeader (i: address) (w: wave) {
  require current_round i > 4 * (w-1)
  -- chooseLeader i w := true
  if ¬ w ∈ chooseLeader i
    then chooseLeader i := chooseLeader i |> List.insert w
  GlobalPerfectCoin w
}

action recv (i: address) {
  let output :| output ∈ r_deliver i
  let (m, j, r) := output
  -- -- require vset.count m.strong > (2 * f + 1)
  -- --   ∨ (r_deliver i m j <&> (·==1)) == some true
  if m.strong.length ≤ (2 * f + 1) ∧ r ≠ 1 then return ()
  let checked := vertex.mk j m.payload.payload
  if (checked, r, m) ∈ recvLog i then return ()
  -- recvLog i checked := (r_deliver i m j).map (·, m)
  recvLog i := recvLog i |> List.insert (checked, r, m)
  DAG_maintain i
}

action send (i: address) {
  let r := current_round i
  let b := a_bcast i r
  let v := vertex.mk i b
  let g := view i
  -- require
  --   ∀ m: message address block
  --   , r_bcast i m ≠ none
  --   → r_bcast i m ≠ some r
  require
    r_bcast i |> (List.all · (fun (_, r') => r' ≠ r))
  require r ≠ 0
  require r = 1 ∨
    ∃ s: nodeSet
    , nset.supermajority s
    ∧ ∀ i: address
      , nset.member i s
      → ∃ v': vertex address block
        , v' ∈ g.nodes
        ∧ ((recvLog i).any (fun (checked, r', _) => checked == v' ∧ r' == r-1))
  let strong := do
    let node <- g.nodes
    let (checked, r', _) <- recvLog i
    if r' == r-1 && node == checked then pure node else []
  let weak := do
    let node <- g.nodes
    let (checked, r', _) <- recvLog i
    if r' < r-1 && node == checked && (node ∉ voted i) then pure node else []
  let m := message.mk v strong weak
    -- (g.nodes.filter
    --   (fun v' => ((·.1 == r-1) <$> recvLog i v') = some true))
    -- (g.nodes.filter
    --   (fun v' => (((fun (r', _) => decide $ r' < r-1) <$> recvLog i v') = some true) ∧ voted i v' = false))
  -- r_bcast i m := some r
  r_bcast i := r_bcast i |> List.insert (m, r)
  -- voted i V := vset.contains V g.nodes
  voted i := g.nodes.insert v
  recvLog i := recvLog i |> List.insert (v, r, m)
  -- let strong_edges
  --   := vset.toList m.strong |> List.map (fun v' => edge.mk v v')
  let strong_edges := strong.map (fun v' => edge.mk v v')
  -- let weak_edges
  --   := vset.toList m.weak |> List.map (fun v' => edge.mk v v')
  let weak_edges := weak.map (fun v' => edge.mk v v')
  -- view i := Graph.mk
  --   (vset.insert v g.nodes)
  --   (strong_edges ++ g.strong)
  --   (weak_edges ++ g.weak)
  view i := Graph.mk (voted i) (strong_edges ++ g.strong) (weak_edges ++ g.weak)
  -- recvLog i v := some (r, m)
}

action getWaveVertexLeader (i: address) (w: wave) {
  require w > 0
  require current_round i ≥ 4 * w
  ChooseLeader i w
  let g := view i
  let mut ret := waveVertexLeader i w
  if ret ≠ none then return ret
  -- if let some j := waveLeader w then
    -- let v
    --   :| v ∈ g.nodes
    --   && (recvLog i |> List.find? (·.1 == v))
    --     <&> (fun (_, r, _) => r == 4 * (w-1) + 1) == some true
    --   && v.source == j
    -- ret := v
    -- for v in g.nodes do
    --   -- if (recvLog i |> List.find? (·.1 == v)) <&> (fun (_, r, _) => r == 4 * (w-1) + 1) == some true then
    --   for (checked, r, msg) in recvLog i do
    --     if r == 4 * (w-1) + 1 then
    --     if checked == v then
    --     if v.source == j then
    --       ret := v
  -- waveVertexLeader i w :=
  return g.nodes.foldl (fun ret v =>
        if (recvLog i).any (fun (checked, r, _)
          => r == 4 * (w-1) + 1
           ∧ checked == v
           ∧ some (v.source) == waveLeader w
        ) then some v else ret
      ) ret
  -- waveVertexLeader i w := ret
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

-- procedure findLog (i: address) (default v': vertex address block) {
--   return ((recvLog i).find?
--     (fun (checked, _, _) => checked == v')).getD (default, 0, message.mk default [] [])
-- }

-- set_option trace.Meta.synthInstance true
def findLog?
  (default: vertex address block)
  (logs: List $ (vertex address block × round × message address block))
  (v': vertex address block)
  [DecidableEq (vertex address block)] :=
  (logs.find?
    (fun (checked, _, _) => decide $ checked = v')).getD (default, 0, message.mk default [] [])
  -- this `getD` will not be triggered, `default` only passed for type

partial def strong_path
  (default: vertex address block)
  (g: Graph address block $ edge address block)
  (logs: List $ (vertex address block × round × message address block))
  (u v: vertex address block)
  [DecidableEq (vertex address block)]
  : Bool :=
  if u == v then true else
  let (u, ur, um) := findLog? default logs u
  let (v, vr, vm) := findLog? default logs v
  if ur ≤ vr then false else
  um.strong.any (fun u' => strong_path default g logs u' v)

partial def path
  (default: vertex address block)
  (g: Graph address block $ edge address block)
  (logs: List $ (vertex address block × round × message address block))
  (u v: vertex address block)
  [DecidableEq (vertex address block)]
  : Bool :=
  if u == v then true else
  let (u, ur, um) := findLog? default logs u
  let (v, vr, vm) := findLog? default logs v
  if ur ≤ vr then false else
  (um.strong ++ um.weak).any (fun u' => path default g logs u' v)

action orderVertices (i: address) (vertices: List $ vertex address block) {
  return ()
}

action waveReady (i: address) (w: wave) {
  require w > 0
  require current_round i ≥ 4 * w
  let wd := decidedWave i
  require w > wd
  -- getWaveVertexLeader i w
  let wo <- getWaveVertexLeader i w
  -- let wo := waveVertexLeader i w
  if wo == none then return ()
  let g := view i
  let v? :| v? ∈ g.nodes
  let v := wo.getD v?
  -- let vl <- findLog i v v
  let logs := recvLog i
  let findLog! := findLog? v logs
  let vl := findLog! v
  -- this `getD` will never fail, v is only assisting the type;
  -- normally we should use the pattern `if let some vl := wo` ,
  -- but #gen_spec denies that??
  -- let findLog := fun v' => ((recvLog i).find?
  --   (fun (checked, _, _) => checked == v')).getD (v, 0, message.mk v [] [])
    -- only call with nodes in g
  let mut leaderStack: List $ vertex address block := []
  let sliceRound := (4: Nat) * w
  let readyVertices := (do
    let u <- g.nodes
    let (_, r, _) := findLog! u
    guard (r == sliceRound)
    guard (strong_path v g logs u v)
    pure v
  )
  let prepare := decide $ readyVertices.length ≥ 2 * f + 1
  if ¬ prepare then return ()
  let loopWaves := (do
    let index <- List.range (w-1 - wd)
    pure $ Fin.ofNat 3 (w-1 - index)
  )
  let (leadersStack, lastLeader) <- loopWaves.foldl
    -- since for-in loop in action does not work well,
    -- now use `foldl` and `bind` to simulate for-in
    (fun last w' => last >>= fun ((leadersStack, v): List (vertex address block) × vertex address block) =>
      getWaveVertexLeader i w' >>= fun v'o =>
      match v'o with
      | none => return (leadersStack, v)
      | some v' =>
        if strong_path v g logs v' v
          then return (leadersStack.insert v', v')
          else return (leadersStack, v)
    )
    -- initial action, returns variables in loop
    $ (pure ([v], v))
  let mut leadersStack := [v]
  let mut vLast := v
  -- for w' in loopWaves veil_do
  --   let v' <- getWaveVertexLeader i w'

  decidedWave i := w
}

action advanceRound (i: address) {
  return ()
}

-- action test_for {
--   let mut l: List Nat := []
--   for i in ([1,2,3]: List Nat) do
--     l := l.insert i
-- }

-- action test_match {
--   match some 2 with
--     | some n => test_ := n
--     | none => return ()
-- }
#gen_spec

#model_check {
  address := Fin (3*1+1)
  nodeSet := ByzNSet (3*1+1)
  block := Fin ((3*1+1) * 3 /- waves-/ * 4 /- 4 rounds each wave-/ )
  -- vtxs := Set $ vertex (Fin 4) (Fin 48)
} {
  f := 1
  a_bcast := fun i r => Fin.ofNat 48 (4 * r + i)
}

-- #check_invariants

end DAG

#check Veil.VeilM.pickSuchThat
