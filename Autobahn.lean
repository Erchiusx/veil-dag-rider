import Veil
set_option linter.dupNamespace false

veil module AutobahnData

abbrev address := Fin 4
abbrev nodeSet := ByzNSet 4

abbrev nset := byzNodeSetFin 4 1 (by simp) (fun x => x == 0) (by simp)

namespace nset
  def empty : nodeSet :=
    ⟨List.nil, List.Pairwise.nil⟩
end nset
instance: Veil.FinEncodableInjOnly nodeSet :=
  let all := allByzNSets 4
  have h : NeZero all.length := by {
    constructor
    simp
    unfold all allByzNSets
    dsimp
    simp [FinEnum.Finset.enum]
  }
  {
    card := all.length
    encode s := Fin.ofNat (all.length) $ (all.findIdx? (· == s)).getD 0
    encode_inj := by {
      unfold Function.Injective
      intros s1 s2

      simp
      have s1e: s1 ∈ all := allByzNSets_complete s1
      have s2e: s2 ∈ all := allByzNSets_complete s2

      have helem: ∀ (s: nodeSet), s ∈ all → ↑s ∈ all.unattach := by
        intros s elem
        exact_mod_cast (by
          simp
          constructor
          rcases s with ⟨s', ps⟩
          simp
          exact ps
          exact elem
        )
      intro hidx
      unfold Option.getD at hidx
      have hs1 := helem s1 s1e
      have hs2 := helem s2 s2e
      have lnn : List.findIdx? (fun x => x == ↑s1) all.unattach ≠ none
        := by
          contrapose hs1
          rw [List.findIdx?_eq_none_iff] at hs1
          contrapose s1e
          apply hs1 at s1e
          simp at s1e
      have rnn : List.findIdx? (fun x => x == ↑s2) all.unattach ≠ none
        := by
          contrapose hs2
          rw [List.findIdx?_eq_none_iff] at hs2
          contrapose s2e
          apply hs2 at s2e
          simp at s2e
      rcases Option.ne_none_iff_exists'.mp lnn with ⟨ol, hol⟩
      rcases Option.ne_none_iff_exists'.mp rnn with ⟨or, hor⟩
      simp [hol, hor] at hidx
      rcases List.findIdx?_eq_some_iff_getElem.mp hol with ⟨ol_range, hl⟩
      rcases List.findIdx?_eq_some_iff_getElem.mp hor with ⟨or_range, rl⟩

      apply Subtype.ext
      rw [List.length_unattach] at ol_range
      rw [List.length_unattach] at or_range
      have holor : ol = or := by
        have hval := congrArg Fin.val hidx
        simp [Nat.mod_eq_of_lt ol_range, Nat.mod_eq_of_lt or_range] at hval
        exact hval

      have hs1_at : all.unattach[ol] = ↑s1 := by
        simpa using hl.1

      have hs2_at : all.unattach[or] = ↑s2 := by
        simpa using rl.1

      calc
        ↑s1 = all.unattach[ol] := hs1_at.symm
        _ = all.unattach[or] := by
          cases holor
          rfl
        _ = ↑s2 := hs2_at
    }
  }

abbrev block := Fin 50

/-
  position 0 is genesis.
  usable positions in this bounded model: 1, 2.
-/
abbrev pos := Fin 3

namespace pos

def genesis : pos := ⟨0, by decide⟩
def one     : pos := ⟨1, by decide⟩
def two     : pos := ⟨2, by decide⟩

/-
  Do NOT use Fin addition for lane positions.
  Fin addition wraps modulo 3, which is wrong for lane sequence numbers.
-/
def isSucc (parent child : pos) : Bool :=
  parent.val + 1 == child.val

def nonGenesis (p : pos) : Bool :=
  decide $ p ≠ genesis

end pos

-- instance: DecidableRel pos.isSucc :=


/-
  Deterministic input for honest nodes.
  We run the model checker for 2 rounds,
  Assuming Byzantine behaviour will take a value in range [13,50)
-/
def input (i : address) (p : pos) : block :=
  Fin.ofNat 50 (p.val * 4 + i.val)

/-
  Data proposal content only.
  PoA is modeled separately by `hasPoA`.
-/
@[veil_decl]
structure proposal where
  source   : address
  position : pos
  parent   : pos
  payload  : block
-- deriving DecidableEq, BEq
deriving instance Veil.Enumeration for proposal
deriving instance Veil.FinEncodableInjOnly for proposal

abbrev lane := Std.ExtTreeMap pos proposal
instantiate lmap : TMap pos proposal lane
instance [lmap: TMap pos proposal lane] : Inhabited lane where
  default := lmap.empty
/-
  Local view:
    view src dst
  means dst's local view of src's lane.
-/
function view   : address → address → lane

/-
  Buffered proposal:
    buffer src dst k
  means dst has received some proposal from src at position k,
  but may not yet have voted / installed it.
-/
function buffer : address → address → pos → Option proposal

/-
  Network-level broadcast fact.
  `broadcasted src p` means p was made available as a proposal from src.
-/
relation broadcasted (src : address) (p : proposal)

/-
  Data-layer vote:
    dataVoted voter p
  means voter signed / voted for proposal p.

  For correct voters, this is guarded by `votedAt`.
  Byzantine voters may vote arbitrarily.
-/
relation dataVoted (voter : address) (p : proposal)

/-
  Correct-voter one-vote guard:
    votedAt voter src pos
  means voter has already voted for some proposal from src at pos.
-/
relation votedAt (voter : address) (src : address) (k : pos)

/-
  PoA certificate.
  `hasPoA p S` means S is a claimed PoA voter set for proposal p.
  The action `make_poa` below only creates this when every member
  in S actually data-voted for p, and S has size f+1.
-/
relation hasPoA (p : proposal) (S : nodeSet)


abbrev slot := Fin 1
abbrev viewNo := Fin 1
abbrev digest := Fin 8

relation prepared  (leader : address) (s : slot) (v : viewNo) (d : digest)
relation prepVoted (voter : address) (s : slot) (v : viewNo) (d : digest)
-- relation votedInView (voter : address) (s : slot) (v : viewNo)
-- relation prepareQC (s : slot) (v : viewNo) (d : digest) (s : nodeSet)

#gen_state
/-
  A proposal is certified iff it has some f+1 PoA.
-/
ghost relation certified (p : proposal) :=
  ∃ S, hasPoA p S ∧ nset.greater_than_third S

/-
  A proposal is syntactically well-formed as a lane extension.
  This deliberately does not constrain payload, because Byzantine owners
  may choose arbitrary payloads.
-/
ghost relation wellFormed (p : proposal) :=
  pos.nonGenesis p.position ∧ pos.isSucc p.parent p.position

/-
  Proposal p is installed in dst's view of src's lane at position k.
-/
ghost relation installed (src dst : address) (k : pos) (p : proposal) :=
  TMap.lookup k (view src dst) = some p

/-
  Parent availability for voting / installing.
  Position 1 extends genesis, so no parent proposal is required.
-/
ghost relation parentKnown (src dst : address) (p : proposal) :=
  p.parent = pos.genesis ∨ ∃ pp, installed src dst p.parent pp

after_init {
  view SRC DST := lmap.empty
  buffer SRC DST K := none

  broadcasted SRC P := false
  dataVoted V P := false
  votedAt V SRC K := false
  hasPoA P S := false

  prepared L S V D := false
  prepVoted R S V D := false
  -- votedInView R S V := false
  -- prepareQC S V D Q := false
}

/-
  Honest owner broadcasts its own next proposal.

  This action captures:
    - correct owner does not equivocate;
    - payload is deterministic;
    - position is a proper successor of parent;
    - for position > 1, the parent must already be known locally.

  It does NOT create a PoA. PoA is produced later by data votes.
-/
action broadcast (i : address) (parent next : pos) {
  require pos.nonGenesis next
  require pos.isSucc parent next

  -- Round 1 extends genesis.
  -- Round 2 extends a locally known certified parent.
  require parent = pos.genesis ∨
    ∃ pp, installed i i parent pp ∧ certified pp

  let p : proposal :=
    ⟨i, next, parent, input i next⟩

  broadcasted i p := true

  -- Owner also receives/knows its own proposal immediately.
  buffer i i next := some p
  view i i := (view i i).insert next p
}

/-
  Byzantine owner can broadcast any syntactically well-formed proposal
  under its own source identity.

  This permits data-lane equivocation:
    same Byzantine source, same position, different payloads.
-/
action byz_broadcast (i : address) (p : proposal) {
  require nset.is_byz i
  require p.source = i
  require wellFormed p

  broadcasted i p := true
  buffer i i p.position := some p
}

/-
  Network delivery into dst's buffer.
  This action does not imply dst has voted.
-/
action receive (src dst : address) (p : proposal) {
  require dst ≠ src
  require broadcasted src p
  require p.source = src
  require wellFormed p

  buffer src dst p.position := some p
}

/-
  Correct data vote.

  A correct voter votes only if:
    - proposal was broadcast by its source;
    - proposal is well-formed;
    - voter has not already voted for this source/position;
    - parent is locally known, unless parent is genesis.

  Voting also installs the proposal in the voter's local view.
-/
action data_vote (voter src : address) (p : proposal) {
  require voter ≠ src
  require broadcasted src p
  require p.source = src
  require wellFormed p
  require parentKnown src voter p

  require ¬ votedAt voter src p.position

  dataVoted voter p := true
  votedAt voter src p.position := true

  buffer src voter p.position := some p
  view src voter := (view src voter).insert p.position p
}

/-
  Byzantine voter can vote arbitrarily.
  It does not update `votedAt`, because `votedAt` is a guard
  for correct voters only.
-/
action byz_data_vote (voter : address) (p : proposal) {
  require nset.is_byz voter

  dataVoted voter p := true
}

/-
  Build a PoA from f+1 data votes.

  This is the key place where we prevent forged PoA:
  every member of S must actually have data-voted for p.
-/
action make_poa (p : proposal) (s : nodeSet) {
  require nset.greater_than_third s
  require ∀ v, nset.member v s → dataVoted v p

  hasPoA p s := true
}


#gen_spec

set_option veil.printCounterexamples true
-- #check_invariants
set_option trace.Meta.synthInstance true in
#model_check {} {}

end AutobahnData
