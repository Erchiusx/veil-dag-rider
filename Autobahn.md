This formalization was developed with assistance from Codex.

# Simplified Autobahn Veil Model

This note documents the current model in `Autobahn.lean`. The model is intentionally small: it is not a full formalization of the Autobahn paper, but a finite Veil model that keeps the safety-relevant shape of Autobahn's data availability layer, fast-path consensus, and view change.

## 1. Simplification

The model uses finite enum domains:

- `address = {n0, n1, n2, n3}`
- `block = {b0, b1}`
- `viewNo = {v0, v1}`
- `pos = {one, two}`

Replica `n0` is the Byzantine replica. Replicas `n1`, `n2`, and `n3` are the honest replicas. The checked consensus value is the position-2 tip of one selected lane, represented as `(src = n1, pos = two, payload = b1)`.

Only the canonical honest lane `n1` is allowed to drive PoA, prepare, and commit in this model. This is a symmetry reduction rather than a protocol restriction: for the safety question "can two honest replicas commit conflicting lane tips?", the names of honest lane owners are interchangeable, so one representative honest lane is enough to exercise the certificate and consensus path. Keeping only one canonical honest lane also avoids duplicating the same proof obligation across symmetric choices of `n1`, `n2`, and `n3`. The model does not assume the network contains no other behavior: Byzantine broadcasts and Byzantine data votes are still present before the PoA boundary, but non-canonical data cannot become the retained consensus certificate because of the active `OnlyCanonicalPoA`, `OnlyCanonicalPrepare`, and `OnlyCanonicalCommit` constraints.

The data layer keeps two positions rather than flattening them into separate relations. A data message is identified by:

```text
(src, pos, payload)
```

The retained data-layer relations are:

- `broadcasted src k payload`
- `dataVoted voter src k payload`
- `votedAt voter src k`
- `hasPoA src k payload`

The retained consensus-layer relations are:

- `currentView replica`
- `prepared view src k payload`
- `prepVoted voter src k payload`
- `consensusVoted voter`
- `commitQC view src k payload`
- `committed src k payload`
- `timeoutCert`

The model keeps the important no-equivocation assumption from the earlier half-work: even a Byzantine replica is not allowed to broadcast two different payloads for the same lane position. This is encoded as an action precondition on both `broadcast` and `byz_broadcast`, and is checked again by the invariant `LaneNoEquivocation`.

The data layer is simplified as follows:

- honest broadcast is represented by `broadcast`, currently restricted to replica `n1` and payload `b1`;
- Byzantine broadcast is represented by `byz_broadcast`, restricted to source `n0`, with either payload;
- position `one` can be broadcast without a prior PoA;
- position `two` requires a PoA for position `one` with the same payload;
- honest data votes are one-shot per `(voter, src, pos)`;
- Byzantine data votes are allowed through `byz_data_vote` without the one-shot restriction;
- `make_poa` abstracts proof-of-availability creation from two data votes.

The consensus layer is simplified as follows:

- there are only two views, `v0` and `v1`;
- `make_timeout_cert` abstracts timeout collection and TC construction;
- `view_change` changes a replica's `currentView` from `v0` to `v1` after the timeout certificate exists;
- `fast_prepare` prepares only position `two`;
- the `v0` leader is `n1`, and the `v1` leader is `n2`;
- `fast_vote` models honest consensus votes and is one-shot per voter;
- `byz_fast_vote` models a Byzantine consensus vote;
- `fast_commit` commits after three distinct prep votes.

This is not DAG-Rider-style total ordering of every node's DAG. The model is an Autobahn-like availability-plus-consensus slice: it checks that a PoA-backed lane tip can move through prepare/vote/commit without conflicting commits.

## 2. State Constraints

`state_constraint` clauses are model-checking filters, not protocol invariants. Veil explores only states satisfying all active state constraints. States violating a state constraint are skipped rather than reported as safety violations.

The current effective model deliberately does **not** constrain:

- `broadcasted`
- `dataVoted`

This is important. Leaving those relations unconstrained lets the model checker explore Byzantine first-position broadcasts and Byzantine votes. Earlier versions constrained these relations to the canonical lane, which made the data layer too trivial and filtered out much of the Byzantine behavior.

The current model keeps only these three constraints:

```lean
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
```

Informally:

- broadcasts and data votes may contain non-canonical and Byzantine behavior;
- only PoAs for lane `n1` and payload `b1` are retained;
- only prepares for `(n1, two, b1)` are retained;
- only commits for `(n1, two, b1)` are retained.

This is the current compromise. It keeps the pre-PoA data layer nontrivial, while cutting the state space at the certificate and consensus layers so the model checker can finish.

## 3. Why The Model Is Nontrivial

The constraints do not directly assert that a commit exists. A committed state can only be reached by executing the protocol actions:

```text
broadcast / byz_broadcast
data_vote / byz_data_vote
make_poa
broadcast position two
data_vote / byz_data_vote
make_poa
make_timeout_cert
view_change
fast_prepare
fast_vote / byz_fast_vote
fast_commit
```

The model includes Byzantine behavior at three points:

- `byz_broadcast` lets `n0` broadcast either block, subject to same-position no-equivocation;
- `byz_data_vote` lets `n0` vote without the honest one-shot vote restriction;
- `byz_fast_vote` lets `n0` add a consensus vote after a prepare exists.

The PoA threshold is simplified to two votes. With four replicas and one Byzantine replica, this corresponds to checking a small `2f + 1`-style quorum slice where at least one honest vote participates. Since `hasPoA` is retained only for `(n1, _, b1)`, non-canonical data behavior can exist but cannot drive the retained consensus certificate.

The consensus path is still meaningful:

- position `two` depends on a PoA for position `one`;
- `fast_prepare` requires the position-2 PoA;
- `fast_vote` requires the prepare and PoA;
- `fast_commit` requires three distinct prep votes;
- active invariants check PoA validity, prepared-value validity, committed-value validity, position discipline, and agreement across views.

The current action coverage can show a misleading `never enabled` warning in the Veil widget. The table is more informative: nonzero `Generated` and `Distinct` counts mean the action generated successor states. In the current run, actions such as `make_poa`, `fast_prepare`, `fast_vote`, `byz_fast_vote`, and `fast_commit` had nonzero generated successor counts, so the consensus path was actually explored.

### Recorded Action Coverage

The following table records the VSCode Veil widget output from the completed compiled `#model_check` run. This was copied from the widget because VSCode does not automatically persist the progress JSON to a file.

The run took 3 hours and 8 minutes. The corresponding metrics are recorded in `metrics.json` in this repository; this file is the saved action generation record for the same run.

| Action | Generated | Distinct |
| --- | ---: | ---: |
| `AutobahnConsensusEffectiveCodex.Label.broadcast` | 2296107 | 206 |
| `AutobahnConsensusEffectiveCodex.Label.byz_broadcast` | 1183064 | 6802 |
| `AutobahnConsensusEffectiveCodex.Label.byz_data_vote` | 3409315 | 246606 |
| `AutobahnConsensusEffectiveCodex.Label.byz_fast_vote` | 1518363 | 149943 |
| `AutobahnConsensusEffectiveCodex.Label.data_vote` | 4295688 | 1062443 |
| `AutobahnConsensusEffectiveCodex.Label.fast_commit` | 7994448 | 142057 |
| `AutobahnConsensusEffectiveCodex.Label.fast_prepare` | 1387386 | 112568 |
| `AutobahnConsensusEffectiveCodex.Label.fast_vote` | 965349 | 234308 |
| `AutobahnConsensusEffectiveCodex.Label.make_poa` | 7211358 | 957 |
| `AutobahnConsensusEffectiveCodex.Label.make_timeout_cert` | 1144836 | 6127 |
| `AutobahnConsensusEffectiveCodex.Label.view_change` | 1893507 | 359843 |

## 4. Active Safety Invariants

The current core invariants are deliberately split into two groups. The first group corresponds to safety conditions that are directly motivated by the Autobahn paper. The second group is introduced by this finite simplification so that the small Veil model has explicit inductive support for the abstracted certificate and consensus path.

Paper-motivated safety invariants:

- `LaneNoEquivocation`: no source broadcasts two different blocks at the same position. This is the retained form of the paper-level signed-lane consistency assumption: a replica's lane should not contain conflicting messages at the same position. The invariant is stronger than the paper-level Byzantine model, because this simplified formalization also applies the no-equivocation assumption to Byzantine replicas.
- `ConsensusAgreementAcrossViews`: two committed values must agree on source, position, and payload. This is the main consensus safety property: view change must not allow conflicting committed lane tips.

Model-introduced invariants for the simplification (and especially for a canonical run):

- `Position2ExtendsPosition1`: a position-2 broadcast requires a position-1 PoA for the same payload. This replaces the full DAG/tip-cut dependency structure with a two-position lane dependency;
- `PreparedHasPoA`: every prepared value has a PoA. This connects the simplified consensus layer back to the abstracted data-availability certificate;
- `PreparedIsPosition2`: every prepared value is a position-2 value. This records that the model checks consensus only for the selected lane tip, not for every data-layer message;
- `CommittedHasPoA`: every committed value has a PoA. This prevents the abstract commit relation from drifting away from availability-backed values;
- `CommittedIsPosition2`: every committed value is a position-2 value. This is the commit-side counterpart of `PreparedIsPosition2`.

These are intentionally core safety properties rather than a large collection of auxiliary inductive invariants. The paper-motivated invariants express the security goal we want to preserve, while the model-introduced invariants are scaffolding caused by the two-position, single-canonical-lane abstraction.

## 5. What Is Abstracted Away

The model abstracts away:

- cryptographic signatures;
- full DAG construction and cut computation;
- batching;
- many positions beyond `one` and `two`;
- detailed timeout messages and high-QC selection;
- liveness and real timeouts;
- network scheduling as an explicit message queue.

Veil explores action interleavings over the finite transition system. Timeout is modeled as an action that creates `timeoutCert`; it is not a real-time event.

The result is a compact Autobahn-like assignment model: it contains a nontrivial data availability certificate, Byzantine behavior, view change, a fast/recovery prepare-vote-commit path, and safety invariants that can be checked by Veil's compiled model checker.
