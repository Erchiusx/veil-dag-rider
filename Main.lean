import Veil
import Examples.Other.ReliableBroadcast

veil module DagRiderBroadcast

type block
type nodeset
type vertexset
type address

-- instance round from an abstract type to Nat
abbrev round := Nat
open Nat

type vertex
class Vertex
  (vertex address block vertexset: Type)
where
  round: vertex → round
  source: vertex → address
  block: vertex → block
  strong: vertex → vertexset
  weak: vertex → vertexset

instantiate v_: Vertex vertex address block vertexset

class VertexSet
  (vertex vset address block: Type)
  [v_: Vertex vertex address block vset]
where
  member (a: vertex) (s: vset) : Prop
  empty: vset
  empty_with_round: round → vset
  round: vset → round

  empty_with_round_def:
    ( ∀ (r: round)
      , round (empty_with_round r) = r
    ) ∧
    ( ∀ (a: vertex) (r: round)
      , ¬ member a (empty_with_round r)
    )

  insert (a: vertex) (s: vset)
    (alignment: s = empty ∨ v_.round a = round s)
    : vset

  insert_contains_a_and_s:
    ∀ (a: vertex)
      (s: vset)
      (alignment:
        s = empty ∨ v_.round a = round s
      )
    , member a (insert a s alignment)
    ∧ ∀ (b: vertex)
      , member b s
      → member b (insert a s alignment)

  supermajority (s : vset): Prop

  round_alignment:
    ∀ (a: vertex) (s: vset)
    , member a s
    → v_.round a = round s

  empty_is_not_supermajority: ¬ supermajority empty
  empty_is_empty: ∀ (a: vertex), ¬ member a empty

instantiate vset : VertexSet vertex vertexset address block

type path
class Path
  (path vertex address block vertexset: Type)
  [v_: Vertex vertex address block vertexset]
  [vset: VertexSet vertex vertexset address block]
where
  member: vertex → path → Prop
  exclusion_round:
    ∀ (p: path)
      (v1 v2: vertex)
    , (member v1 p ∧ member v2 p)
    → v_.round v1 ≠ v_.round v2

  top: path → vertex
  bottom: path → vertex

  top_bottom_elem:
    ∀ (p: path)
    , member (top p) p
    ∧ member (bottom p) p

  connected:
    ∀ (p: path)
    , ∀ (v: vertex)
      , member v p
      → v = top p
      ∨ ∃ (v': vertex)
        , member v' p
        ∧ ( vset.member v' (v_.strong v)
          ∨ vset.member v' (v_.weak v)
          )

  round_bound:
    ∀ (p: path) (v: vertex)
    , member v p
    → v_.round v ≥ v_.round (bottom p)
    ∧ v_.round v ≤ v_.round (top p)


instantiate path_: Path path vertex address block vertexset

variable (is_byz : address → Prop)
instantiate nset : NodeSet address is_byz nodeset
open NodeSet

type view
class View
  (view vertex vertexset address block: Type)
  [v_: Vertex vertex address block vertexset]
  [vset: VertexSet vertex vertexset address block]
where
  current: view → vertexset
  past: view → Option view
  round: view → round

  next (v: view): view

  empty: view
  empty_view_def:
    current empty = vset.empty
    ∧ past empty = none
    ∧ round empty = 1

  only_empty_view_has_no_past:
    ∀ (v: view)
    , past v = none ∨ round v = 1
    → current v = vset.empty

  next_def:
    ∀ (v: view)
    , current (next v) = vset.empty
    ∧ past (next v) = some v
    ∧ round (next v) = round v + 1

  height_view:
    ∀ (v: view)
    , match past v with
      | none => round v = 1
      | some v' => round v = round v' + 1

  positivity:
    ∀ (v: view)
    , round v > 0

  round_alignment:
    ∀ (v: view)
    , current v = vset.empty
    ∨ round v = vset.round (current v)

instantiate view_: View view vertex vertexset address block

relation current_round (a: address) (r: round)

relation has'view (a: address) (v: view)
relation view'slice (a: address) (s: vertexset)
relation received (a: address) (v: vertex)
#gen_state

#print State

def vertex'in'view
  (v: vertex) (view': Option view): Prop :=
  match view' with
  | none => False
  | some view
    => vset.member v (view_.current view)
    ∨ vertex'in'view v (view_.past view)
  termination_by match view' with
    | none => 0
    | some v => view_.round v
  decreasing_by {
    cases h: view_.past v' with
    | none =>
        simp
        exact (view_.positivity v')
    | some v1 =>
        simp
        have h1 := view_.height_view v'
        rw [h] at h1
        simp at h1
        rw [h1]
        simp
  }

def path'in'dag (p: path) (v: view): Prop :=
  ∀ (v': vertex)
  , path_.member v' p
  → vset.member v' (view_.current v)
  ∨ vertex'in'view block vertexset address vertex view v' (view_.past v)

after_init {
  current_round A N         := False
  current_round A 0         := True
  has'view A V              := False
  has'view A view_.empty    := True
  received A V              := False
  view'slice A S            := False
}

action advance_round_slice
  (a: address)
  (r: round) = {
  require current_round a r
  require
    ∀ (s: vertexset)
    , view'slice a s
    ∧ vset.round s = r
    → vset.supermajority s
  current_round a r := False
  current_round a (r + 1) := True
}

action advance_round
  (a: address)
  (r: round)
  (v: view) = {
  require current_round a r
  require has'view a v
  require vset.supermajority (view_.current v)
  require
    ∃ (v': vertex)
    , vset.member v' (view_.current v)
    ∧ v_.source v' = a
  current_round a r := False
  current_round a (r + 1) := True
  has'view a v := False
  has'view a (view_.next v) := True
}



action send
  (v: vertex)
  (a: address)
  (vi: view)
  (vi': view) = {
  -- check that the sender owns the view and the vertex
  require has'view a vi
  require v_.source v = a
  -- the vertex differs from the vertices in the view
  require
    ∀ (v': vertex)
    , vset.member v' (view_.current vi)
    → v_.source v' ≠ a
  -- the strong set should be the parent view's all edges
  require v_.strong v = match view_.past vi with
    | none => vset.empty
    | some past_view => view_.current past_view
  let vertex'in'view'judgement :=
    vertex'in'view block vertexset address vertex view
  require
    ∀ (v0: vertex)
    , vset.member v0 (v_.weak v)
    ↔ ¬ ∃ (p: path)
      , path_.top p = v
      ∧ path_.bottom p = v0
      ∧ ∀ (v1: vertex)
        , path_.member v1 p
        → (v1 ≠ v0 ∧ vset.member v1 (v_.weak v))
        ∨ vertex'in'view'judgement v1 (some vi)
  /- the vertex should be from the current round
    here we require this alignment, and we will use it as `sorry`
    in the insertion
  -/
  require v_.round v = view_.round vi
  -- all checks passed, we can send the vertex

  -- vi' is the modified view after vi
  require
    view_.current vi'
    = vset.insert v (view_.current vi)
    ( by {
      have round_alignment
        : v_.round v = view_.round vi := by sorry
      have h := view_.round_alignment vi
      rw [round_alignment]
      cases h with
      | inl h1 =>
          rw [h1]
          simp
      | inr h2 =>
          rw [h2]
          simp
    })
  require
    view_.past vi' = some vi

  has'view a vi := False
  has'view a vi' := True
}

action receive
  (a: address)
  (v: vertex)
  (vi: view) = {
  require has'view a vi

}

#gen_spec

set_option veil.printCounterexamples true
#check_invariants

end DagRiderBroadcast
