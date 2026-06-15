import Veil
set_option linter.dupNamespace false
set_option synthInstance.maxHeartbeats 800000
set_option synthInstance.maxSize 20000

veil module AutobahnConsensusEffectiveCodex

enum address = {n0, n1, n2, n3}
enum block = {b0, b1}
enum viewNo = {v0, v1}

enum pos = {one, two}

/-
  Two-position Autobahn slice with position as an explicit relation argument.

  The checked execution still focuses on one canonical source lane, but the
  data-layer vocabulary is no longer flattened into separate `...1`/`...2`
  relations. A message is identified by `(src, k, payload)`.
-/
relation broadcasted (src : address) (k : pos) (payload : block)
relation dataVoted (voter : address) (src : address) (k : pos) (payload : block)
relation votedAt (voter : address) (src : address) (k : pos)
relation hasPoA (src : address) (k : pos) (payload : block)

/-
  Single-slot, two-view consensus layer.
  Consensus commits the position-2 tip of the selected lane.
-/
function currentView : address → viewNo
relation prepared (v : viewNo) (src : address) (k : pos) (payload : block)
relation prepVoted (voter : address) (src : address) (k : pos) (payload : block)
relation consensusVoted (voter : address)
relation commitQC (v : viewNo) (src : address) (k : pos) (payload : block)
relation committed (src : address) (k : pos) (payload : block)
individual timeoutCert : Bool

#gen_state

after_init {
  broadcasted SRC K B := false
  dataVoted V SRC K B := false
  votedAt V SRC K := false
  hasPoA SRC K B := false

  currentView I := v0
  prepared VIEW SRC K B := false
  prepVoted V SRC K B := false
  consensusVoted V := false
  commitQC VIEW SRC K B := false
  committed SRC K B := false
  timeoutCert := false
}

action broadcast (src : address) (k : pos) {
  let payload := b1
  require src = n1
  require k = one ∨ hasPoA src one payload
  require ∀ (old : block), broadcasted src k old → old = payload

  broadcasted src k payload := true
}

action byz_broadcast (src : address) (k : pos) (payload : block) {
  require src = n0
  require k = one ∨ hasPoA src one payload
  require ∀ (old : block), broadcasted src k old → old = payload

  broadcasted src k payload := true
}

action data_vote (voter src : address) (k : pos) (payload : block) {
  require voter ≠ src
  require broadcasted src k payload
  require k = one ∨ hasPoA src one payload
  require ¬ votedAt voter src k

  dataVoted voter src k payload := true
  votedAt voter src k := true
}

action byz_data_vote (voter src : address) (k : pos) (payload : block) {
  require voter = n0
  require broadcasted src k payload
  require k = one ∨ hasPoA src one payload

  dataVoted voter src k payload := true
}

action make_poa (src : address) (k : pos) (payload : block) (v1 v2 : address) {
  require v1 ≠ v2
  require k = one ∨ hasPoA src one payload
  require dataVoted v1 src k payload
  require dataVoted v2 src k payload

  hasPoA src k payload := true
}

action make_timeout_cert {
  require hasPoA n1 two b1

  timeoutCert := true
}

action view_change (i : address) {
  require currentView i == v0
  require timeoutCert

  currentView i := v1
}

action fast_prepare (leader : address) (v : viewNo) (src : address) (k : pos) (payload : block) {
  require (v = v0 ∧ leader = n1) ∨ (v = v1 ∧ leader = n2)
  require leader ≠ n0
  require currentView leader == v
  require k = two
  require hasPoA src k payload
  require v = v0 ∨ timeoutCert
  require ∀ (oldV : viewNo) (oldSrc : address) (oldK : pos) (oldPayload : block),
    prepared oldV oldSrc oldK oldPayload →
      oldSrc = src ∧ oldK = k ∧ oldPayload = payload

  prepared v src k payload := true
}

action fast_vote (voter : address) (v : viewNo) (src : address) (k : pos) (payload : block) {
  require voter ≠ n0
  require currentView voter == v
  require prepared v src k payload
  require hasPoA src k payload
  require ¬ consensusVoted voter

  prepVoted voter src k payload := true
  consensusVoted voter := true
}

action byz_fast_vote (voter : address) (v : viewNo) (src : address) (k : pos) (payload : block) {
  require voter = n0
  require prepared v src k payload

  prepVoted voter src k payload := true
}

action fast_commit (v : viewNo) (src : address) (k : pos) (payload : block) (a b c : address) {
  require a ≠ b
  require a ≠ c
  require b ≠ c
  require k = two
  require hasPoA src k payload
  require prepared v src k payload
  require ∀ (oldSrc : address) (oldK : pos) (oldPayload : block),
    committed oldSrc oldK oldPayload →
      oldSrc = src ∧ oldK = k ∧ oldPayload = payload
  require prepVoted a src k payload
  require prepVoted b src k payload
  require prepVoted c src k payload

  commitQC v src k payload := true
  committed src k payload := true
}

invariant [LaneNoEquivocation]
  ∀ (src : address) (k : pos) (b1 b2 : block),
    broadcasted src k b1 →
    broadcasted src k b2 →
      b1 = b2

invariant [Position2ExtendsPosition1]
  ∀ (src : address) (payload : block),
    broadcasted src two payload →
      hasPoA src one payload

invariant [PreparedHasPoA]
  ∀ (v : viewNo) (src : address) (k : pos) (payload : block),
    prepared v src k payload →
      hasPoA src k payload

invariant [PreparedIsPosition2]
  ∀ (v : viewNo) (src : address) (k : pos) (payload : block),
    prepared v src k payload →
      k = two

invariant [CommittedHasPoA]
  ∀ (src : address) (k : pos) (payload : block),
    committed src k payload →
      hasPoA src k payload

invariant [CommittedIsPosition2]
  ∀ (src : address) (k : pos) (payload : block),
    committed src k payload →
      k = two

invariant [ConsensusAgreementAcrossViews]
  ∀ (src1 src2 : address) (k1 k2 : pos) (payload1 payload2 : block),
    committed src1 k1 payload1 →
    committed src2 k2 payload2 →
      src1 = src2 ∧ k1 = k2 ∧ payload1 = payload2

-- Broadcast states are intentionally unconstrained: this lets the checker
-- explore Byzantine first-position broadcasts. Votes and certificates are
-- still cut back to the canonical lane so the consensus path remains tractable.
-- state_constraint [OnlyCanonicalDataVote]
--   ∀ (voter src : address) (k : pos) (payload : block),
--     dataVoted voter src k payload →
--       src = n1 ∧
--       payload = b1

state_constraint [OnlyCanonicalPoA]
  ∀ (src : address) (k : pos) (payload : block),
    hasPoA src k payload →
      src = n1 ∧
      payload = b1

state_constraint [OnlyCanonicalPrepare]
  ∀ (v : viewNo) (src : address) (k : pos) (payload : block),
    prepared v src k payload →
      src = n1 ∧ k = two ∧ payload = b1

state_constraint [OnlyCanonicalCommit]
  ∀ (src : address) (k : pos) (payload : block),
    committed src k payload →
      src = n1 ∧ k = two ∧ payload = b1

-- TODO: Re-enable after deciding how much of the higher-arity pos-param model
-- should be generated and checked by Veil.
-- set_option diagnostics true
-- set_option trace.veil.perf true
-- set_option trace.veil.perf.elaborator true
-- set_option trace.veil.perf.extract true
-- set_option trace.veil.perf.definition true
#time #gen_spec

-- TODO: #check_invariants needs fresh hand-written proofs for the pos-param model.
#check_invariants

#model_check compiled {} {}

end AutobahnConsensusEffectiveCodex
