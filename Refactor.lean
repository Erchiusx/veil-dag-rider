import Veil


veil module DAG

type node
instantiate inst_node: LE node
instantiate decLE_node: DecidableRel inst_node.le

type nodeset
instantiate nset: ByzNodeSet node nodeset

type block

abbrev round := Nat
abbrev wave := Nat
immutable individual maxRound: round
immutable function a_bcast: node → round → block

@[veil_decl]
structure vertex (node block: Type) where
  source: node
  payload: block
  round: round

type vertexSet
type vertexPairSet
instantiate vset: TSet (vertex node block) vertexSet
instantiate edge: TSet (vertex node block × vertex node block) vertexPairSet
@[veil_decl]
structure message (vtx vtxs: Type) where
  payload: vtx
  strong: vtxs
  weak: vtxs

@[veil_decl] structure Graph (vtx vtxs pairs: Type) where
  nodes: vtxs
  strong: pairs
  weak: pairs
-- strong and weak sets are pairs of edges, fst -> snd
-- we will maintain this relationship
function current_round: node → round
function view: node → Graph (vertex node block) vertexSet vertexPairSet

relation r_bcast: node → message (vertex node block) vertexSet → round → Bool
relation r_deliver: node → message (vertex node block) vertexSet → round → node → Bool

relation chooseLeader: node → wave → Bool
function waveLeader: wave → Option node

function decidedWave: node → wave
relation delivered: node → vertex node block → Bool

relation a_deliver_at: node → block → round → node → wave → Bool
#gen_state

-- -- v1 -> v2
-- ghost relation connected (i: node) (v1 v2: vertex node block) :=
--   ∃ p: List $ vertex node block
--   , p ⊆ (view i).nodes
--   ∧ v1 ∈ p
--   ∧ v2 ∈ p
--   ∧ ( ∀ v: vertex node block
--       , v ∈ p
--       → v = v1
--       ∨ v.round < v1.round
--       ∧ ∃ v': vertex node block
--         , v' ∈ p
--         ∧ (v', v) ∈ (view i).strong ∪ (view i).weak
--     )

-- ghost relation strongly_connected (i: node) (v1 v2: vertex node block) :=
--   ∃ p: List $ vertex node block
--   , p ⊆ (view i).nodes
--   ∧ v1 ∈ p
--   ∧ v2 ∈ p
--   ∧ ( ∀ v: vertex node block
--       , v ∈ p
--       → v = v1
--       ∨ v.round < v1.round
--       ∧ ∃ v': vertex node block
--         , v' ∈ p
--         ∧ (v', v) ∈ (view i).strong
--     )

after_init {
  current_round N := 0
  view N := Graph.mk vset.empty edge.empty edge.empty

  r_bcast I M R := false
  r_deliver I M R K := false

  chooseLeader N W := false
  waveLeader W := none

  decidedWave N := 0
  delivered N V := false

  a_deliver_at I M R K W := false
}



invariant [DAG_structure]
  ∀ (n: node) (p q: vertex node block)
  , let g := view n
  ; p ∈ g.nodes
  ∧ (p, q) ∈ edge.union g.strong g.weak
  → q ∈ g.nodes

#gen_spec

-- #model_check {
--   node := Fin (3 * 1 + 1)
--   nodeset := ByzNSet (3 * 1 + 1)
-- } {}
#check_invariants

end DAG
