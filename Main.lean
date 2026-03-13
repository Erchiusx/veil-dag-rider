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

type vertex
-- structure vertex where
--   round: round
--   source: address
--   block: block
--   strong: vertexset
--   weak: vertexset
relation vertex'fields
  (v: vertex)
  (r: round)
  (b: block)
  (strong: vertexset)
  (weak: vertexset)

class VertexSet (vertex: Type) (vset: Type) where
  is_empty (s: vset): Prop
  member (a: vertex) (s: vset) : Prop
  empty: vset

  supermajority (s : vset): Prop

  empty_is_empty:
    is_empty empty
  supermajority_nonempty:
    ∀ (s : vset), supermajority s → ¬ is_empty s

instantiate vset : VertexSet vertex vertexset

variable (is_byz : address → Prop)
instantiate nset : NodeSet address is_byz nodeset
open NodeSet


-- structure DAG'view where
--   current'round'vertices: vertexset
--   past'round: Option DAG'view
type DAG'view
relation DAG'view'fields
  (view: DAG'view)
  (current: vertexset)
  (past: Option DAG'view)


relation current_round (a: address) (r: round)

-- seems impossible to correctly initialize a individual f,
-- so maybe we need to pass f as an argument to every action?
-- individual f : Nat

-- how about individual dag'view'map : Std.HashMap round (DAG'view vertexset)
relation has'view (a: address) (v: DAG'view)
variable (empty'view: DAG'view)



#gen_state

ghost relation ready'for'next'round
  (a: address)
  (v: DAG'view)
  (r: round)
  (s: vertexset)
  (p: Option DAG'view)
  := current_round a r
  ∧ has'view a v
  ∧ DAG'view'fields v s p
  ∧ vset.supermajority s

#print State

after_init {
  current_round A 0 := True
  current_round A N := False
  has'view A empty'view := True
  has'view A V := False
  -- view and vertex construction
  vertex'fields V R B S W := False
  DAG'view'fields empty'view C Option.none := True
  DAG'view'fields V C P := False
}

-- action advance_round (a: address) (r: round) (v: DAG'view vertexset)= {
--   require ready'for'next'round a r v
--   current_round a r := False
--   current_round a (r+1) := True
--   has'view a v := False
--   has'view a (DAG'view.mk vset.empty v) := True
-- }

-- safety [round_exist_unique]
--   ( ∀ (a: address), ∃ (r: round),
--     current_round a r ) ∧
--   ( ∀ (a: address) (r1 r2: round),
--     current_round a r1 ∧ current_round a r2
--     → r1 = r2)

-- safety [view_exist_unique]
--   ( ∀ (a: address), ∃ (v: DAG'view vertexset),
--     has'view a v) ∧
--   ( ∀ (a: address) (v1 v2: DAG'view vertexset),
--     has'view a v1 ∧ has'view a v2
--     → v1 = v2)

-- view and vertex work like structures
-- safety [vertex_structure]

#check_invariants

end DagRiderBroadcast
