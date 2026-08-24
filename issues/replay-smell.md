# Retire the parallel replay proof engine

## Violated invariant

`Proof` must be the sole owner of proof-semantic state and the sole authority
for advancing it. The kernel remains the authority for primitive logical, C,
memory, and resource semantics; `Proof` is the checked orchestration boundary
through which those operations change a proof.

Explicit tactics apply named simple steps or audited structural operations to
`Proof`. Smart tactics search by applying those same operations to persistent
`Proof` descendants. A successful descendant retains the exact
surface-expressible provenance of the operations that produced it. Extracting
that provenance is serialization: it must not rediscover a proof from semantic
aftermath or rerun search.

Ordinary verification must not construct and independently replay a second
certificate before accepting work already checked through `Proof`. Expansion
instead extracts the selected provenance from a completed `Proof`, renders it
as ordinary Surface Click, rewrites the source, and verifies the rewritten
source through the normal verification entry point before emitting it. This is
the independence boundary that checks extraction, rendering, parsing,
lowering, and source interpretation without retaining a second proof engine.

An internal `ProofCertificate`-like tree may remain as a surface serialization
format. It carries no semantic authority and should be materialized only when
surface proof text or an equivalent inspection result is requested. A source
or expansion cursor may retain source locations, goal identities, provenance
checkpoints, and diagnostic paths, but it must not own independent facts,
`CState`, resources, execution frontiers, branch outcomes, or proof-building
authority.

## Transitional implementation

`Proof` already owns persistent typed goals, facts, execution state, and the
private provenance nodes connecting every accepted successor to its checked
operation. Its focus, split records, and ancestry checkpoints are typed
cursors into that state rather than alternate semantic representations.

`ProofReplayContext` remains a parallel representation around this completed
model. Explicit function-proof verification constructs it and threads it by
value through `execute_internal_proof`. `TacticReplayState` owns an execution
frontier and substantial logical, branch, scope, outcome, effect, deferral,
and proof-construction bookkeeping while `ProofReplayContext` separately owns
`CState`, a fact vector, and branch history. Several operations construct a
temporary `Proof` from this context and then export the checked result back
into replay-owned state.

Legacy smart paths also construct `ProofCertificate` values, replay them
through `execute_internal_proof`, and merge the resulting replay contexts.
The former whole-claim and whole-contract acceptance gates have been removed:
ordinary verification no longer synthesizes a completed proof's surface form
and verifies the claim again. Leading proposition scopes, including quantified
goals, now use the recursive `Proof` source capability directly rather than a
second admission list that could route supported checked operations to replay.
Loop structural-effect checking likewise applies every recursively simple
operation, including nested `have` scopes, to the preservation path's typed
effect `Proof`; only effect scripts containing structural scopes or induction
still cross that compatibility boundary.
The remaining compatibility boundaries are the duplicated proof engine to
remove; independent internal certificate replay is not an invariant to
preserve.

This is not a canonicalization issue. It concerns proof-state ownership and
the final removal of adapters left by the proof-object migration.

## Evidence exposed by the stack issue

`execute_internal_proof` recursively interprets `InternalProofNode` values.
On the ordinary expansion canary
`selected_pure_case_split_simp_expands_by_removal`, its maximum observed live
depth is nine. Before the bounded stack repair, each debug replay frame used
about 123 KiB because it reserved many large replay-context temporaries. Merely
boxing the embedded `TacticReplayState` approximately halved that frame.

The stack failure was repaired independently with a bounded-depth guard and a
small-stack regression. Preserve that regression while removing the machinery
it currently measures; do not weaken the stack bound or grant verifier threads
oversized stacks during the migration.

## Migration constraints

- Start each ordinary proof unit with one checker-owned `Proof`. Interpret
  explicit simple tactics by applying their corresponding checked operation to
  that value.
- Interpret branches, scopes, joins, outcomes, effects, and loop phases through
  typed `Proof` goals and audited structural operations. A syntax driver may
  choose the current source node or focused goal, but it cannot assemble a
  semantic successor.
- Run smart search transactionally over persistent `Proof` descendants. A
  smart success is the completed descendant itself, not a candidate
  certificate awaiting compatibility replay.
- Retain source attribution on checked provenance so expansion can select one
  tactic's contribution after the complete proof unit succeeds. Empty
  contributions remain valid when a smart tactic needed no explicit step.
- Extract structured surface steps from provenance. Do not infer them from
  final facts, execution paths, resources, or outcomes, and do not rerun a
  planner during extraction.
- Verify the complete rewritten source through the ordinary entry point before
  `click expand` writes output. `click audit` may add fixed-point, cold-run, and
  performance checks, but it uses the same verification boundary.
- Keep diagnostic context and source locations sufficient to preserve useful
  failures. Compatibility wording is not a reason to retain semantic replay
  state.

If a source tactic currently performs semantic work that cannot be expressed
as a `Proof` operation, add the missing named audited operation. Do not keep a
general mutable replay escape hatch. An unrelated missing resource or language
operation remains a separate issue rather than being folded into this
architectural migration.

## Intended regressions

### One transition authority

Verify representative explicit and smart proofs covering pure reasoning, C
execution, logical and C branches, resource scopes, calls/effects, loop phases,
and function outcomes. Instrument semantic successor construction and assert
that every successor is produced by `Proof::apply_step` or a named audited
structural operation, with no parallel mutation of replay-owned semantic
state.

### No ordinary certificate replay

Assert that ordinary verification of representative smart proofs performs no
surface-certificate, compatibility, whole-claim, or whole-contract replay.
The checked `Proof` descendant is accepted directly and its provenance is not
materialized merely to establish validity.

### Independent rewritten-source rejection

Expand representative smart proofs and verify the complete rewritten source
normally. Corrupt one rendered simple operation in each representative family
and confirm ordinary verification rejects it at the corresponding checked
`Proof` operation. Expansion success must not make its emitted source
self-authenticating.

### Provenance-only extraction

Assert that expansion returns the steps attributed to the selected source site
from the completed `Proof` lineage, including nested branches and scopes.
Extraction may traverse provenance and surface metadata but must not invoke
semantic transitions, planners, or kernel proof search.

### State ownership census

Add a source-level or instrumentation census proving that production source
interpretation and expansion do not construct or advance
`ProofReplayContext`, directly mutate replay-owned `CState` or fact
collections, or maintain a second execution frontier. Surviving cursors must
have their non-semantic fields individually justified.

### Deterministic scaling

Measure explicit source checking and expansion extraction over increasing
linear proof lengths and branching proofs. Work and allocation must be
proportional to the source, retained proof delta, and emitted surface output,
up to the documented indexing factors. The replacement must not clone complete
proof states or histories per step.

## Acceptance criteria

- Ordinary explicit and smart verification advance one `Proof` through checked
  simple or structural operations and do not construct or replay a separate
  certificate as an acceptance gate.
- `ProofReplayContext`, `execute_internal_proof`, compatibility certificate
  replay, whole-claim/whole-contract replay gates, and parallel semantic or
  certificate builders are deleted.
- Any surviving source, focus, diagnostic, or expansion cursor contains no
  independent proof-semantic state and cannot construct a semantic successor.
- Every accepted smart operation retains exact surface-expressible provenance;
  expansion serializes that provenance rather than reconstructing it from
  semantic aftermath.
- `click expand` verifies the complete rewritten source through ordinary
  verification before output, and `click audit` retains its fixed-point,
  independent-entry-point, and performance guarantees.
- Explicit invalid source and deliberately corrupted expansions are rejected
  by the corresponding audited `Proof` operation.
- Representative pure, execution, branch, scope, loop, outcome, and effect
  regressions pass without compatibility replay.
- Multi-size regressions satisfy the repository's verification-efficiency
  contract, and `scripts/check.sh` is green.
- User and internal documentation describes checked `Proof` transitions and
  verified expansion rather than ordinary certificate replay.
- This file and its Open-list line are deleted when the parallel replay model,
  its obsolete adapters, regressions, and documentation are complete.
