# Replay is a second proof engine

## Violated invariant

Click should have one audited model for advancing a proof. A smart tactic may
search over immutable `Proof` values, and an independently supplied or
expanded certificate must still be checked, but certificate checking should
interpret recorded operations through the same audited proof transitions. It
should not require a second large mutable state machine that separately owns
the C state, facts, execution frontier, branch provenance, and certificate
bookkeeping.

Today `ProofReplayContext` remains that parallel representation. The completed
proof-object migration retired it as a smart-tactic interface, but explicit
source verification and expansion replay still thread it by value through
`execute_internal_proof`. `TacticReplayState` carries execution-frontier and
proof-construction metadata while the context separately carries `CState`, a
fact vector, and branch history. Replay code converts between this state and
proof-object state at multiple boundaries.

Independent checking is required; this issue does not propose trusting an
expansion because the smart tactic that produced it succeeded. The smell is
that independent checking appears to be a second operational proof model
rather than a thin interpreter of the same checked `Proof` operations.

This is not a canonicalization issue. It concerns proof-state ownership and
the relationship between certificate interpretation and the audited proof
object API.

## Evidence exposed by the stack issue

`execute_internal_proof` recursively interprets `InternalProofNode` values.
On the ordinary expansion canary
`selected_pure_case_split_simp_expands_by_removal`, its maximum observed live
depth is nine. Before the bounded stack repair, each debug replay frame used
about 123 KiB because it reserved many large replay-context temporaries. Merely
boxing the embedded `TacticReplayState` approximately halved that frame.

The stack failure can and should be repaired independently with bounded depth,
a small-stack regression, and mundane representation fixes. Do not make this
architectural issue a prerequisite for retiring
`expansion-replay-recursion-exhausts-the-stack.md`, and do not hide the stack
failure by granting verifier threads oversized stacks.

## Questions to resolve first

- Which fields of `ProofReplayContext` are genuine certificate-interpreter
  cursors, and which duplicate state already owned by `Proof`?
- Can explicit source and serialized certificates be interpreted by applying
  their recorded simple and structural operations to a checker-owned `Proof`?
- Which current replay operations perform semantic work not expressible by an
  audited proof-object operation? Those are missing checked operations, not a
  reason for a general mutable replay escape hatch.
- Does certificate extraction still need to run during independent checking,
  or can the checker retain only source locations and diagnostics while the
  checked `Proof` records derivation structure?
- Can branch, scope, join, outcome, and effect traversal share the proof
  object's goal structure without trusting certificate-supplied goal sets or
  rediscovering smart-tactic choices?

## Intended regressions

### One transition authority

Check representative explicit and expanded certificates for pure reasoning,
C execution, branches, resource scopes, calls/effects, and function outcomes.
Instrument every semantic successor and assert that it is produced by
`Proof::apply_step` or a named audited structural proof operation, with no
parallel mutation of a replay-owned semantic state.

### Independent rejection

Corrupt one recorded operation in each representative certificate and confirm
that independent verification rejects it at the corresponding audited proof
operation. Removing the parallel replay model must not make expansion success
self-authenticating.

### State ownership census

Add a source-level or instrumentation census proving that production
certificate interpretation does not construct or advance
`ProofReplayContext`, directly mutate `CState` or fact collections, or maintain
a second execution frontier. Diagnostic cursors and source-location stacks are
allowed, but they must not be semantic authority.

### Deterministic scaling

Measure explicit certificate checking over increasing linear proof lengths and
branching certificates. Work and allocation must be proportional to the
certificate and retained proof delta, up to the documented indexing factors;
the replacement must not clone complete proof states or histories per step.

## Acceptance criteria

- The required independence boundary is documented: certificates are checked
  separately from smart-tactic search, but through the same audited proof
  transitions.
- `ProofReplayContext` and the semantic portions of `TacticReplayState` are
  deleted, or any surviving replay type is a thin non-semantic interpreter
  cursor whose fields are individually justified.
- Explicit source verification, `click expand` verification, and `click audit`
  retain their current independent rejection guarantees and diagnostics.
- Branching, scopes, joins, outcomes, and effects are checked through
  proof-object goal structure rather than a caller-assembled parallel state.
- No semantic transition is accepted by directly editing replay-owned
  `CState`, facts, resources, frontiers, or certificate builders.
- Multi-size regressions satisfy the repository's verification-efficiency
  contract, and `scripts/check.sh` is green.
- This file and its Open-list line are deleted when the duplicated replay
  model and its obsolete adapters are removed.
