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
-- class Vertex (vertex: Type) where
--   round: vertex → round
--   source: vertex → address
--   block: vertex → block
--   strong: vertex → vertexset
--   weak: vertex → vertexset

mutable relation vertex'fields
  (v: vertex)
  (source: address)
  (r: round)
  (b: block)
  (strong: vertexset)
  (weak: vertexset)

class VertexSet (vertex: Type) (vset: Type) where
  member (a: vertex) (s: vset) : Prop
  empty: vset

  insert (a: vertex) (s: vset): vset

  insert_has_subset:
    ∀ (a: vertex) (s: vset),
      member a (insert a s)
      ∧ (∀ (b: vertex), member b s → member b (insert a s))

  supermajority (s : vset): Prop

  empty_is_not_supermajority: ¬ supermajority empty
  empty_is_empty: ∀ (a: vertex), ¬ member a empty

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
relation allocated_view (v: DAG'view)
relation allocated_vertex (v: vertex)

relation sent (n: address) (r: round)
relation cached (n: address) (v: vertex)
relation delivered (n: address) (originator: address) (in_round: round) (v: vertex)


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
  current_round A N         := False
  current_round A 0         := True
  has'view A V              := False
  has'view A empty'view     := True
  -- view and vertex construction
  DAG'view'fields V C P     := False
  DAG'view'fields
    empty'view
    vset.empty
    Option.none             := True
  allocated_view V          := False
  allocated_view empty'view := True
  allocated_vertex V        := False
  vertex'fields V A R B S W := False
  sent N R                  := False
  cached N R              := False
  delivered N O R V         := False
}

action advance_round
  (a: address)
  (r: round)
  (v: DAG'view)
  (s: vertexset)
  (p: Option DAG'view)
  (v': DAG'view) = {
  -- require ready'for'next'round a v r s p
  /- why does this meet the error `unknown metavariable`
    require ready'for'next'round a v r s p
unknown metavariable '?_uniq.58816'
(kernel) declaration has metavariables 'DagRiderBroadcast.advance_round.genI'
(kernel) declaration has metavariables 'DagRiderBroadcast.advance_round.genI.eq_1'
  -/

  require current_round a r
  require has'view a v
  require DAG'view'fields v s p
  require vset.supermajority s

  current_round a r := False
  current_round a (r+1) := True
  has'view a v := False
  -- allocate new view and bind to `a`
  require ¬ allocated_view v'
  allocated_view v' := True
  has'view a v' := True
  DAG'view'fields v' vset.empty (Option.some v) := True
}

action construct_vertex
  (v: vertex)
  (a: address)
  (r: round)
  (b: block)
  (strong: vertexset)
  (weak: vertexset)
  (view: DAG'view)
  (current: vertexset)
  (p: Option DAG'view)= {
  require ¬ allocated_vertex v
  allocated_vertex v := True
  require DAG'view'fields view current p
  require
    ( p = Option.none ∧ strong = vset.empty) ∨
    ( ∃ (view': DAG'view)
    , p = Option.some view'
    ∧ ∃ p': Option DAG'view
      , DAG'view'fields view' strong p'
    )
  require
    ( ∀ (v': vertex)
      , member v' weak
      → ∃ (path: vertexset)
        , ∀ (v1 v2: vertex)
          , member v1 path ∧ member v2 path
          →
    )
  vertex'fields v a r b strong weak := True
}



-- action send
--   (a: address)
--   (r: round)
--   (b: block)
--   (v: vertex)
--   (view: DAG'view)
--   (c: vertexset)
--   (p: Option DAG'view)
--   (weak: vertexset)= {
--   require ¬ sent a r
--   require has'view a view
--   require DAG'view'fields view c p
--   -- allocate new vertex and bind to `a` and `b`
--   require ¬ allocated_vertex v
--   -- compute strong and weak edges
--   let strong := c
--   sent a r := True
--   require
--     ( ∀ (v': vertex)
--       , member v'c
--       → )
--   construct_vertex v r b strong weak
-- }

action receive
  (a: address)
  (v: vertex)
  (source: address)
  (b: block)
  (r: round)
  (strong: vertexset)
  (weak: vertexset) = {
  require allocated_vertex v
  require vertex'fields v source r b strong weak

}

safety [round_exist]
  ( ∀ (a: address), ∃ (r: round),
    current_round a r )
safety [round_exist_unique]
  ( ∀ (a: address) (r1 r2: round),
    current_round a r1 ∧ current_round a r2
    → r1 = r2)

safety [view_exist]
  ( ∀ (a: address), ∃ (v: DAG'view),
    has'view a v)
safety [view_exist_unique]
  ( ∀ (a: address) (v1 v2: DAG'view),
    has'view a v1 ∧ has'view a v2
    → v1 = v2)

-- view and vertex work like structures
safety [vertex_structure_exist]
  ( ∀ (v: vertex),
    ( ¬ allocated_vertex v
      ∧ ∀ (r: round)
          (a: address)
          (b: block)
          (s: vertexset)
          (w: vertexset)
        , ¬ vertex'fields v a r b s w
    )
    ∨ ( allocated_vertex v
      ∧ ∃ (r: round)
          (a: address)
          (b: block)
          (s: vertexset)
          (w: vertexset)
        , vertex'fields v a r b s w
      )
  )
safety [vertex_structure_unique]
  ( ∀ (v: vertex)
      (a1 a2: address)
      (r1 r2: round)
      (b1 b2: block)
      (s1 s2: vertexset)
      (w1 w2: vertexset),
    vertex'fields v a1 r1 b1 s1 w1
    ∧ vertex'fields v a2 r2 b2 s2 w2
    → a1 = a2 ∧ r1 = r2 ∧ b1 = b2 ∧ s1 = s2 ∧ w1 = w2
  )


safety [DAGview_structure_exist]
  ( ∀ (v: DAG'view),
    ( ¬ allocated_view v
      ∧ ∀ (c: vertexset)
          (p: Option DAG'view)
        , ¬ DAG'view'fields v c p
    )
    ∨ ( allocated_view v
      ∧ ∃ (c: vertexset)
          (p: Option DAG'view)
        , DAG'view'fields v c p
      )
  )
safety [DAGview_structure_unique]
  ( ∀ (v: DAG'view)
      (c1 c2: vertexset)
      (p1 p2: Option DAG'view)
    , DAG'view'fields v c1 p1
    ∧ DAG'view'fields v c2 p2
    → c1 = c2 ∧ p1 = p2
  )

safety [DAG_contain_only_allocated_vertices]
  ( ∀ (view: DAG'view) (v: vertex) (c: vertexset) (p: Option DAG'view)
    , DAG'view'fields view c p
    ∧ vset.member v c
    → allocated_vertex v
  )

#gen_spec

set_option veil.printCounterexamples true
#check_invariants

end DagRiderBroadcast
