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
  roundOf: vertex → round
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
  empty: round → vset
  roundOf: vset → round

  insert (a: vertex) (s: vset)
    (alignment: v_.roundOf a = roundOf s)
    : vset

  insert_contains_a_and_s:
    ∀ (a: vertex)
      (s: vset)
      (alignment:
        v_.roundOf a = roundOf s
      )
    , member a (insert a s alignment)
    ∧ ∀ (b: vertex)
      , member b s
      → member b (insert a s alignment)

  supermajority (s : vset): Prop

  round_alignment:
    ∀ (a: vertex) (s: vset)
    , member a s
    → v_.roundOf a = roundOf s

  empty_is_not_supermajority:
    ∀ (r: round)
    , ¬ supermajority (empty r)
  empty_is_empty:
    ∀ (a: vertex) (r: round)
    , ¬ member a (empty r)

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
    → v_.roundOf v1 ≠ v_.roundOf v2

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
    → v_.roundOf v ≥ v_.roundOf (bottom p)
    ∧ v_.roundOf v ≤ v_.roundOf (top p)
instantiate path_: Path path vertex address block vertexset

type vcache
class VCache (vcache vertex: Type) where
  member: vertex → vcache → Prop
  empty: vcache
  insert (v: vertex) (c: vcache) (membership: ¬ member v c): vcache
  delete (v: vertex) (c: vcache) (membership: member v c): vcache

  insertion:
    ∀ (v: vertex) (c: vcache) (h: ¬ member v c)
    , member v (insert v c h)

  deletion:
    ∀ (v: vertex) (c: vcache) (h: member v c)
    , ¬ member v (delete v c h)

  left_invert:
    ∀ (v: vertex) (c: vcache) (h: member v c)
    , insert v (delete v c h) (deletion v c h) = c

  right_invert:
    ∀ (v: vertex) (c: vcache) (h: ¬ member v c)
    , delete v (insert v c h) (insertion v c h) = c

  empty_is_empty:
    ∀ (v: vertex)
    , ¬ member v empty

  select (c: vcache) (h: c ≠ empty):
    Σ (v: vertex) (c: vcache), member v c

instantiate vc: VCache vcache vertex

variable (is_byz : address → Prop)
instantiate nset : NodeSet address is_byz nodeset
open NodeSet

relation current_round (a: address) (r: round)

relation view'slice (a: address) (s: vertexset)
relation received (a: address) (v: vertex)
relation cached (a: address) (c: vcache)
#gen_state

#print State

after_init {
  current_round A N         := False
  current_round A 0         := True
  received A V              := False
  view'slice A S            := False
  cached A C                 := False
  cached A vc.empty          := True
}

action advance_round_slice
  (a: address)
  (r: round) = {
  require current_round a r
  require
    ∀ (s: vertexset)
    , view'slice a s
    ∧ vset.roundOf s = r
    → vset.supermajority s
  current_round a r := False
  current_round a (r + 1) := True
  view'slice a (vset.empty (r+1)) := True
}

action send
  (a: address)
  (last: vertexset)
  (current: vertexset)
  (v: vertex)
  (r: round) = {
  require current_round a r
  require vset.roundOf last + 1 = r
  require vset.roundOf current = r
  require vset.roundOf current = v_.roundOf v
  let h
    : vset.roundOf current = v_.roundOf v
    := sorry -- by requirement
  require view'slice a last
  require view'slice a current
  require
    ∀ (v': vertex)
    , vset.member v' last
    → v_.source v' ≠ a
  require v_.strong v = last
  require
    ∀ (v': vertex)
    , vset.member v' (v_.weak v)
    ↔ ¬ ∃ (p: path)
        , (path_.top p) = v
        ∧ (path_.bottom p) = v'
        ∧ ∀ (mid: vertex)
          , mid = v
          ∨ mid = v'
          ∨ vset.member mid (v_.weak v)
          ∨ ∃ (s: vertexset)
            , view'slice a s
            ∧ vset.member mid s
  view'slice a current := False
  view'slice a
    ( vset.insert v current ( by rw[h] ) ) := True
}

action cache
  (a: address)
  (v: vertex)
  (c: vcache) = {
  require cached a c
  if ¬ vc.member v c
    then
      let h : ¬ vc.member v c := sorry
      -- here if we use if h: ¬ vc.member v c
      -- then h becomes a weird assumption rather than
      -- being ¬ vc.member v c,
      -- which is quite strange
      cached a c := False
      cached a (vc.insert v c ( by
        exact h
      )) := True
}

action gc (a: address) (c: vcache) = {
  if ¬ (c = vc.empty)
    then
      let h: ¬ (c = vc.empty) := sorry
      let h'
        : ∃ (v: vertex), vc.member v c
        := sorry
      match h' with
      | intro v' hv => return ()
}


action receive
  (a: address)
  (r: round)
  (v: vertex)
  (s: vertexset)
  (c: vcache)= {
  require cached a c
  if
    ∃ (v': vertex)
    , received a v'
    ∧ v_.roundOf v = v_.roundOf v'
    then
      return ()
  if
    ∃ (v': vertex)
    , (vset.member v' (v_.strong v) ∨ vset.member v' (v_.weak v))
    ∧ received a v' = False
    then
      cache a v c
      return ()
  if v_.roundOf v > r
    then
      cache a v c
      return ()

  require vset.roundOf s = v_.roundOf v
  let h : vset.roundOf s = v_.roundOf v := sorry
  view'slice a s := False
  view'slice a (vset.insert v s ( by rw [h] )) := True

  gc a

}


#gen_spec

set_option veil.printCounterexamples true
#check_invariants

end DagRiderBroadcast
