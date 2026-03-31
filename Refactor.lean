import Veil
set_option trace.Meta.synthInstance true


veil module DAG

type node
-- instantiate inst_node: LE node
-- instantiate decLE_node: DecidableRel inst_node.le

-- type nodeset
-- instantiate nset: ByzNodeSet node nodeset

type block

abbrev round := Nat
abbrev wave := Nat
-- immutable individual maxRound: round
-- immutable function a_bcast: node → round → block

@[veil_decl]
structure vertex (node block: Type) where
  source: node
  payload: block
  -- round: round

-- @[veil_decl]
-- structure message (node block: Type) where
--   payload: (node × block × round)
--   strong: List $ (node × block × round)
--   weak: List $ (node × block × round)

@[veil_decl]
structure edge (node block: Type) where
  top: vertex node block
  bottom: vertex node block

@[veil_decl]
structure Graph (node block: Type) where
  nodes: List $ vertex node block
  strong: List $ edge node block
  weak: List $ edge node block
-- strong and weak sets are pairs of edges, fst -> snd
-- we will maintain this relationship
-- function current_round: node → round
function view: node → Graph node block
-- -- function view: node → (List $ (node × block × round))


-- relation r_bcast: node → message node block → round → Bool
-- relation r_deliver: node → message node block → round → node → Bool

-- relation chooseLeader: node → wave → Bool
-- function waveLeader: wave → Option node

-- function decidedWave: node → wave
-- relation delivered: node → (node × block × round) → Bool

-- relation a_deliver_at: node → block → round → node → wave → Bool
#gen_state

after_init {
  -- current_round N := 0
  view N := Graph.mk [] [] []

  -- r_bcast I M R := false
  -- r_deliver I M R K := false

  -- chooseLeader N W := false
  -- waveLeader W := none

  -- decidedWave N := 0
  -- delivered N V := false

  -- a_deliver_at I M R K W := false
}

action empty {
  require True
}

safety [DAG_structure]
  ∀ (n: node) (e: edge node block)
  , let g := view n
  ; e.top ∈ g.nodes
  ∧ e ∈ g.strong ∪ g.weak
  → e.bottom ∈ g.nodes

set_option trace.Meta.synthInstance true
#gen_spec

-- #model_check {
--   node := Fin (3 * 1 + 1)
--   nodeset := ByzNSet (3 * 1 + 1)
-- } {}
#check_invariants

end DAG
