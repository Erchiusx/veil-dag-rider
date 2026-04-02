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
abbrev wave := Nat
instantiate instw: LE wave
instantiate decLEw: DecidableRel instw.le
instantiate ordw: Ord wave

type vtxs

@[veil_decl]
structure vertex (address block: Type) where
  source: address
  payload: block
deriving instance Veil.Enumeration for vertex
-- we need to quantify over vertices,
-- so the round parameter is separated from the vertex type
instantiate vset: TSet (vertex address block) vtxs

@[veil_decl]
structure message (address block vtxs: Type) where
  payload: vertex address block
  strong: vtxs
  weak: vtxs
deriving instance Veil.Enumeration for message

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

relation a_deliver_at: address → block → round → address → wave → Bool

function recvLog: address → (checked: vertex address block) → Option (round × (message address block vtxs))
-- when receiving, set the `recvLog` of the vertex from the r_deliver
relation voted: address → vertex address block → Bool

immutable individual f: Nat
#gen_state

after_init {
  current_round I := 0
  view I := Graph.mk vset.empty [] []

  r_bcast I M := none
  r_deliver I M J := none

  chooseLeader I W := false
  waveLeader W := none

  a_deliver_at I B R A W := false

  recvLog I V := none
}

action DAG_maintain (i: address) {
  let g := view i
  let v
   :| recvLog i v ≠ none
    ∧ ¬ vset.contains v g.nodes
  view i :=
    if let some (r, m) := recvLog i v then
      if
        let timecheck := decide (r ≤ current_round i)
        let deps := vset.union m.strong m.weak |> vset.toList
        let depscheck := decide $
          ∀ v': vertex address block
          , v' ∈ deps
          → vset.contains v' g.nodes
        let majority_escape := r == 0
        let majority := decide $
          (m.strong |> vset.count) > 2 * f + 1
        let validity := decide $
          ∀ v': vertex address block
          , v' ∈ m.strong
          → (recvLog i v')
            <&> ( fun (r', _) => r' + 1 == r
            ) = some true
        ; timecheck
       && (majority_escape || majority)
       && validity
       && depscheck
      then
        let strong_edges
          := vset.toList m.strong |> List.map (fun v' => edge.mk v v')
        let weak_edges
          := vset.toList m.weak |> List.map (fun v' => edge.mk v v')
        ; Graph.mk
          (vset.insert v g.nodes)
          (strong_edges ++ g.strong)
          (weak_edges ++ g.weak)
      else
        g
    else g
}

action ReliableBroadcast (i: address) (j: address) {
  let m :| r_bcast i m ≠ none ∧ r_deliver j m i = none
  r_deliver j m i := r_bcast i m
}

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

action recv (i: address) (m: message address block vtxs) {
  let j :| r_deliver i m j ≠ none
  let checked := vertex.mk j m.payload.payload
  recvLog i checked := (r_deliver i m j).map (·, m)
  DAG_maintain i
}

action send (i: address) {
  let r := current_round i
  let b := a_bcast i r
  let v := vertex.mk i b
  let g := view i
  require
    ∀ m: message address block vtxs
    , r_bcast i m ≠ none
    → r_bcast i m ≠ some r
  require r ≠ 0
  require r = 1 ∨
    ∃ s: nodeSet
    , nset.supermajority s
    ∧ ∀ i: address
      , nset.member i s
      → ∃ v': vertex address block
        , vset.contains v' g.nodes
        ∧ (·.1 == r-1) <$> recvLog i v' = some true
  let m
   := message.mk v
    (vset.filter g.nodes
      (fun v' => ((·.1 == r-1) <$> recvLog i v') = some true))
    (vset.filter g.nodes
      (fun v' => (((fun (r', _) => decide $ r' < r-1) <$> recvLog i v') = some true) ∧ voted i v' = false))
  r_bcast i m := some r
  voted i V := vset.contains V g.nodes
  let strong_edges
    := vset.toList m.strong |> List.map (fun v' => edge.mk v v')
  let weak_edges
    := vset.toList m.weak |> List.map (fun v' => edge.mk v v')
  view i := Graph.mk
    (vset.insert v g.nodes)
    (strong_edges ++ g.strong)
    (weak_edges ++ g.weak)
  recvLog i v := some (r, m)
}



action waveReady (i: address) (w: wave) {
  return ()
}

action advanceRound (i: address) {
  return ()
}

end DAG
