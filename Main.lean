import Veil
import Examples.Other.ReliableBroadcast

veil module DagRiderBroadcast

type block
type nodeset
type vertexset
type address

-- instance round from an abstract type to Nat
abbrev round := Nat
abbrev count := Nat
open Nat


structure vertex where
  round: round
  source: address
  block: block
  strong: vertexset
  weak: vertexset
deriving DecidableEq

class VertexSet (vertex: Type) (vset: Type) where
  is_empty (s: vset): Prop
  member (a: vertex) (s: vset) : Prop
  empty: vset

  supermajority (s : vset): Prop

  empty_is_empty:
    is_empty empty
  supermajority_nonempty:
    ∀ (s : vset), supermajority s → ¬ is_empty s

instantiate vset : VertexSet (vertex address block vertexset) vertexset

variable (is_byz : address → Prop)
instantiate nset : NodeSet address is_byz nodeset
open NodeSet


structure DAG_view where
  current_round_vertices: vertexset
  past_round: Option DAG_view


relation current_round (a: address) (r: round)

-- seems impossible to correctly initialize a individual f,
-- so maybe we need to pass f as an argument to every action?
-- individual f : Nat

-- how about individual dag_view_map : Std.HashMap round (DAG_view vertexset)
relation has_view (a: address) (v: DAG_view vertexset)


#gen_state

ghost relation ready_for_next_round (a: address) (v: DAG_view vertexset) (r: round)
  := current_round a r
  ∧ has_view a v
  ∧ vset.supermajority v.current_round_vertices

#print State

after_init {
  current_round A 0 := True
  current_round A N := False
  -- has_view A (DAG_view.mk vset.empty Option.none) := True
  -- has_view A V := False
}

-- action advance_round (a: address) (r: round) (v: DAG_view vertexset) = {
--   require current_round a r
--   require has_view a v
--   require vset.supermajority v.current_round_vertices
--   current_round a r := False
--   current_round a (r+1) := True
--   has_view a v := False
--   has_view a (DAG_view.mk vset.empty v) := True
-- }

safety [round_exist]
  ( ∀ (a: address), ∃ (r: round),
    current_round a r )
safety [round_unique]
  ( ∀ (a: address) (r1 r2: round),
    current_round a r1 ∧ current_round a r2
    → r1 = r2)

-- safety [view_exist]
--   ( ∀ (a: address), ∃ (v: DAG_view vertexset),
--     has_view a v)
-- safety [view_unique]
--   ( ∀ (a: address) (v1 v2: DAG_view vertexset),
--     has_view a v1 ∧ has_view a v2
--     → v1 = v2)

#check_invariants

end DagRiderBroadcast
