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

This section is historical evidence for the replacement architecture. The
work plan is the Architecture correction below plus the census and design
sections that follow it; do not treat the shapes recorded here as a queue.

`Proof` owns persistent typed goals and the private provenance nodes connecting
accepted successors to checked operations. However, its execution model is not
yet an independent replacement for replay. `Proof::for_execution_frontier`
still consumes a `ProofReplayContext`, and its internal `ExecutionProofState`
embeds almost the complete `TacticReplayState`. That payload still contains the
execution frontier, program-point states, branch-completion markers, loop
rules, effect facts, planned transitions, freshness counters, deferred source
operations, and a parallel certificate builder.

Explicit function-proof verification also constructs `ProofReplayContext`
directly and threads it by value through `execute_internal_proof`.
`ProofReplayContext` separately owns `CState`, a fact vector, and branch
history. Several operations construct a temporary `Proof` from this context
and then export the checked result back into replay-owned state. Consequently,
putting an operation behind a `Proof` method does not by itself establish sole
state ownership while that method reads and rewrites the embedded replay
payload.

Legacy smart paths also construct `ProofCertificate` values, replay them
through `execute_internal_proof`, and merge the resulting replay contexts.
The former whole-claim and whole-contract acceptance gates have been removed:
ordinary verification no longer synthesizes a completed proof's surface form
and verifies the claim again. Leading proposition scopes, including quantified
goals, now use the recursive `Proof` source capability directly rather than a
second admission list that could route supported checked operations to replay.
Loop structural-effect checking likewise applies every recursively simple
operation, including nested `have` and `open` resource scopes, to the
preservation path's typed effect `Proof`. A terminal frame inside nested
resource scopes stays on that `Proof` while the checked representations close;
it is discharged only by the outer scope and is never replayed. Proposition
proofs inside those `have` scopes use the same recursive authoritative driver,
including nested proof `if` and `cases`, whether the `have` is top-level or
inside an open resource. A terminal proof `if` tree below any number of leading
open resources also stays on one sibling-goal `Proof`: terminal leaves may open
further resources, close every representation from inner to outer, and retire
their own goals before the recursive joins retain exact nested
`Open(...Open(If(...If(...))...))` provenance. Prefix operations before a
deeper leading scope come from that scope's checked root lineage rather than
being reconstructed during serialization. Proof-level execution `if` and
logical `cases` trees also stay on `Proof` with no enclosing resource. The
non-semantic source cursor consumes only an exact `if` prefix aligned with an
already-certified C path; every remaining `if` and `cases` branch is checked
through audited sibling-goal splits and joins. A `cases` split checks its exact
available disjunction and gives each persistent sibling only its own disjunct,
without recording semantic path state in a replay cursor. Thus all supported
leading loop-effect scopes compose on `Proof`, and structural-effect checking
has no compatibility replay fallback. Induction, a C `branch` at the loop
back-edge effect goal, and nested-loop certificate variants are rejected as
invalid effect operations rather than treated as migration targets.
The remaining compatibility boundaries are the duplicated proof engine to
remove; independent internal certificate replay is not an invariant to
preserve. The completed shape-specific paths above remain useful regressions,
but they are evidence for the replacement architecture rather than a queue of
more shapes to migrate one at a time.

This is not a canonicalization issue. It concerns proof-state ownership and
the final removal of adapters left by the proof-object migration.

## Architecture correction after the shape-by-shape migration

The first migration strategy moved individual surface shapes onto `Proof`:
flat functions, grouped functions, calls, resource scopes, structural effects,
and selected branch forms each acquired a direct `try_check_*` path while
`execute_internal_proof` remained as a fallback. This produced local checked
paths, but it did not converge on deletion. Every combination of proof unit,
scope, branch shape, loop phase, smart tactic, and expanded tactic required a
new admission grammar and another fallback boundary.

The reverted `Keep linear loop preservation on Proof` experiment made the
problem concrete. Its regression inferred preservation replay from a claim
label ending in `.loop(0).preserve`; a frontier-local loop uses the enclosing
label such as `count_to_three.contract`, so the test was a false negative. An
exact counter at the preservation fallback showed that the supposedly direct
linear proof still called `execute_internal_proof` once. A recursive branch
variant then verified only through that fallback, while its expanded explicit
branch failed with `then branch arm has not reached its shared continuation`.
The commit and its inaccurate issue claim were reverted rather than retained
as an unused speculative adapter.

The root missing operation is a first-class execution region on `Proof`.
Whole-function execution has a distinguished exit, but loop preservation must
execute an arbitrary nested C region and stop at one exact back-edge. Today
that boundary is represented by a synthetic sentinel plus replay-owned
continuation and `completed_branch_regions` bookkeeping. Nested branch joins
therefore cannot compose solely by typed goal and split identity. Adding more
loop- or branch-specific syntax drivers would preserve this defect.

### Corrected migration order

1. Introduce a typed Proof-owned execution-region goal and boundary identity.
   Function exit, branch join, loop back-edge, and nested-region return must be
   instances of the same checked boundary mechanism.
2. Move semantic frontier, region, branch, loop, effect, and freshness state
   out of `TacticReplayState` into that typed Proof state. Leave source
   locations, expansion selection, and diagnostics in a non-semantic cursor.
3. Drive `InternalProofNode` through one compositional source interpreter.
   Linear operations, scopes, branches, nested loops, and continuations must
   return a `Proof` at a typed boundary rather than export a replay context.
4. Move provenance construction entirely to `ProofNode` ancestry and source
   attribution, then remove `proof_certificate_builder` and semantic path
   reconstruction from replay state.
5. Migrate and delete whole compatibility boundaries. A chunk counts as
   architectural progress only when it deletes a fallback, semantic replay
   field, or parallel interpreter path; adding another guarded `try_check_*`
   path while retaining its fallback is not completion.
6. Instrument exact compatibility call sites. Claim labels, total execution
   counts, or baseline comparisons are supporting diagnostics, not proof that
   a particular fallback was avoided.

## State census (2026-08-24)

Taken after `proof_object.rs` was mechanically split into concern modules.
The replay adapters (`for_execution_frontier`,
`for_execution_frontier_with_effect_goals`, `start_loop_effect_goal`,
`into_execution_context`, `finalization_view`) are co-located in
`src/lang/click/proof/proof_object/replay_boundary.rs`, so step 5 deletes
one file rather than hunting scattered methods.

### `TacticReplayState` fields by ownership

`TacticReplayState` (`replay_state.rs:135`) has 36 fields. Line references
are as of this census date.

Semantic fields whose destination is typed `Proof` state: `loop_effect_goal`
(subsumed by the typed region boundary's effect payload), `frontier`,
`effect_facts` (joins already compute typed `introduced_effect_facts`
deltas), `case_assumptions`, `next_opaque_call` and `next_kernel_variable`
(freshness counters, snapshotted even inside `PlannedStatementTransition`),
`execution_start_facts`, `function_entry_execution_prerequisites` and
`function_entry_derivations` (typed per-step deltas already exist on
`ExecutionProofStepDelta`), `unfolded_predicates` (a typed duplicate already
lives in `GoalContext`; delete the replay copy), `frontier_loop_clauses`,
`frontier_loop_rules`, `function_entry_state`, `concrete_loop_execution`,
`execution_abstraction`, `region_invariants_closed` (becomes discharge of a
typed invariant-bundle obligation), and the semantic half of
`program_point_states` (named `CState` snapshots; the point keying survives
as source attribution).

Semantic fields whose destination is deletion: `proof_certificate_builder`
(step 4, with dependents `next_path_choice`, `open_scopes`,
`planned_statement_transitions`), `completed_branch_regions` and
`has_structured_branch_history` (replaced by typed split/region identity),
`post_execution_tactics` and `ordered_finalization` (compatibility
boundaries of the exit drain), and `region_proof` /
`loop_invariant_region` (mode flags that become region identity).

Cursor fields that survive in the non-semantic cursor: `proof_site`,
`source_layout`, `region_simp`, `invariant_closer_step`,
`has_resource_surface_history`, `grouped_contract`,
`deferred_tactic_capture`, `deferred_expansion_path_choices`, and the
diagnostic `branch_path` on both context structs. `surface_propositions` is
serialization metadata (every recovered candidate is re-validated by exact
equality) but currently sits on the checking hot path; it becomes surface
attribution attached to provenance with no checking authority.

`ExecutionProofState` (`proof_object.rs:1060`) already holds the
destination shapes: `state` (the Proof-owned `CState`), `branch_decisions`
and `outcome_branch_decisions` (output-sized provenance), and
`last_step_delta` (the typed export mechanism). Its embedded `replay` field
dissolves per the lists above; `has_empty_execution_branch_leaf` deletes
with the compatibility routing it gates.

### Replay call-site map

`execute_internal_proof` (`replay_engine/proof_execution.rs:2576`) has four
production entry points, plus its internal recursion:

- `claim_proofs.rs:797` — single-claim fallback once
  `try_check_structural_function_proof` / `try_check_flat_function_proof`
  decline; also every generated smart script (`auto`, `frame`, `simp`).
- `claim_proofs.rs:1013` — the grouped whole-contract equivalent.
- `loop_planning.rs:1303` — every loop preservation proof, explicit or
  planned, via the synthetic sentinel frontier.
- `loop_planning.rs:433` — automatic preservation planning: a worklist
  search that replays one-tactic programs per candidate, then merges
  certificates that are re-verified through the previous site — the
  construct-then-replay double engine in one place.

Nothing is expansion-only: `click expand` threads capture state through the
identical verification paths, so every site above is on ordinary
verification.

`tactic_replay.rs` contains roughly twenty wrap/op/unwrap round trips
(`try_smart_step_on_proof` and friends, plus inline per-tactic arms): each
constructs a `ProofReplayContext` from loose locals, builds a `Proof` via
`for_execution_frontier`, applies one checked operation, exports the state
back through `into_execution_context`, and pushes the certificate steps
into `proof_certificate_builder`. These are pure step-2 casualties; no
individual site needs its own migration.

`finalization_view` has three readers: the ordered outcome drain
(`claim_proofs.rs:1521`), deferred expansion capture
(`have_proofs.rs:2063`), and a non-semantic timing read
(`proof_execution.rs:796`) that only needs the cursor split.

Dependency summary: step 1 unblocks both `loop_planning.rs` sites and the
interpreter's `Branch` join; step 2 removes every `tactic_replay.rs` round
trip and lets the `try_check_*` roots start as `Proof`; step 3 deletes
`execute_internal_proof` and `OrderedProofUnit::Replay`; step 4 retires the
`proof_certificate_builder` reads inside finalization; step 5 deletes
`replay_boundary.rs` and `ProofReplayContext` itself.

### Boundary representations the typed region goal must subsume

The execution position is not a `Proof` concept today.
`ProofExecutionPoint` (`replay_state.rs:1897`) has exactly three states —
`FunctionEntry`, `StatementEntry`, `FunctionExit` — with no region or
back-edge variant, and `FrontierGoal` (`proof_object.rs:1297`) carries only
an effect selection and context: "execute to function exit", "execute this
arm to its join", and "execute the loop body to the back-edge" are
indistinguishable by type. The four boundary kinds are encoded three
different ways:

- Function exit: the `FunctionExit` enum variant (holding the outcome
  candidates inside the position itself), plus the caller-side invariant
  `continuations.len() <= initial_continuation_depth` re-checked at every
  terminal join.
- Branch join: `completed_branch_regions` membership, and stack depth back
  at the split's `initial_continuation_depth`, and
  `frontier.next_statement_index` equal to the layout's continuation node —
  three replay-state observables mutated by side effect. Sibling identity
  (`SplitId`, arm `GoalId`s, `Arc::ptr_eq` markers) already exists on
  `Proof` and is sound; only the C-level boundary is untyped.
- Loop back-edge: structural equality of the remaining program with a
  synthetic `return 0` sentinel plus an empty continuation stack
  (`loop_planning.rs:1266` and `:1343`); the loop-effect obligation is a
  mutable `closed` boolean rather than goal discharge.
- Scope return: `Arc`-pointer ancestry on `Proof` (sound) duplicated by the
  replay continuation stack and the `open_scopes` counter, with scope close
  deferred through `post_execution_tactics` when the frontier is already at
  exit.

## Typed execution-region boundary: design draft

Replay encodes "stop here" by keeping code beyond the boundary in the
frontier — the function tail after a branch arm, a synthetic sentinel after
a loop body — and then checking after the fact that execution did not run
past. The typed replacement inverts this: an execution-region goal owns
exactly the region's statement tree, so completion is structural exhaustion
of the goal's own frontier, and executing past the boundary is
unrepresentable rather than detected.

Shape:

- `FrontierGoal` gains a typed region identity — function body, branch arm
  (keyed by `SplitId` and arm position), or loop body (keyed by loop index)
  — and a typed boundary stating what is due at completion: function exit
  carries per-path outcome obligations, a branch join carries the join
  interface at its split identity, and a loop back-edge carries the
  invariant bundle and structural-effect obligations.
- A region goal completes in one of two typed states: at-boundary (its
  statement tree is exhausted — by construction, since it owns no code past
  the boundary) or terminal (a `return` retired the path into typed outcome
  candidates). Joins accept mixed arms, as `branch ensuring` already does;
  terminal arms contribute outcome candidates that propagate to the parent
  region.
- Joins compose by split identity and marker ancestry alone: both sibling
  goals at-boundary for the same split lets an audited join re-derive the
  parent's region goal owning the shared continuation. No completed-region
  set, no depth comparison, no statement-index comparison.
- Nested regions are nested goals rather than stacked continuations; the
  `ExecutionFrontier` continuation stack dissolves into the goal tree, and
  `initial_continuation_depth` fields disappear from the split records.
- Loop preservation constructs a loop-body region goal directly — no
  sentinel, no `region_proof` / `loop_invariant_region` flags. Preservation
  obligations discharge against the boundary payload.
- `SourceExecutionLayout`, `CodeRegionRef`, and `ProgramPointRef` survive as
  cursor attribution describing where a region sits in source; they no
  longer decide completion.

Validation order, per the corrected migration order: the loop back-edge
landed first, because the census showed function exit already has a typed
variant while the back-edge was the boundary encoded as synthetic C. The
frontier now carries a typed `ExecutionRegionKind`; exhausting a
`LoopBody` region's own statement tree installs the typed
`ProofExecutionPoint::RegionBoundary`, and the sentinel plus its
structural-equality `at_back_edge` check are deleted. The regression
`body_final_branch_preservation_completes_at_typed_back_edge_boundary`
pins the shape the sentinel was masking: a body-final C `if` whose arms
and join complete at the boundary with no code behind it.

Branch joins landed next. `completed_branch_regions`, the `Branch`
continuation kind, `initial_continuation_depth` on every split record,
and the dynamic arm-overshoot guard are deleted; the continuation stack
now carries only loop iterations. `SourceExecutionLayout` carries true
control-flow successors (arm-final statements chain to their enclosing
`if`'s continuation) plus the statically derived set of branch regions
each statement completes, so branch-region exits need no runtime
bookkeeping. C `if` arms have two modes: path-following flows (decided
steps, bounded exploration, and the whole legacy engine) splice the
selected arm inline before the `if`'s tail, while Proof-side sibling
splits are bounded — the arm frontier owns exactly the arm's own
statement tree, joins compose on the typed boundary by split identity,
and the parent frontier is restored by the join. Terminal-style arms
that legitimately continue to function exit consume one explicit
escape per region level (`continue_arm_into_parent_frontier`), driven
by the split record; an arm that escaped is no longer at the boundary,
so the checked-join predicates still enforce the join discipline.
Next: unify function exit and the back-edge as instances of one
boundary mechanism when the frontier migrates onto `Proof` (step 2).
Each chunk scores by the replay field or fallback it deletes, never by
adding a guarded path beside a retained fallback.

## Scoped composite population is a replay-state witness

The scoped composite population reproduction formerly tracked separately
belongs to this issue because it is not a separate resource-language defect.
Opening and closing an allocation-bearing composite is a checked
representation change. After the scope closes, the subsequent opaque-call
transition must begin from the same live resources and counted populations as
the Proof-owned state and fresh kernel certification.

In `examples/owned-vector/vector.click`, replacing the persistent
`observe(allocated_vector(owner))` in the full-capacity branch of
`allocated_vector_push` with an `open(allocated_vector(owner)) { ... }` scope
allows the preparatory steps to finish and closes the representation before
the existing multi-successor-aware call step. The successful `vector_grow`
path then exposes the mismatch: parallel replay retains both the consumed and
returned allocations, plus stale populations for `allocation`,
`vector_storage`, and `allocated_vector`, while fresh kernel certification
retires the consumed allocation. The paths disagree before final resource
representation checking.

The intended reduced regression uses a small allocation-bearing composite,
opens and closes it before a verified call with failure and success outcomes,
and has success return a distinct allocation while retiring the input. The
Proof-owned successor and fresh certification must agree on live and retired
allocations and counted populations on every outcome. This reproduction must
be repaired by removing the parallel state transition, not by adding a scoped
population patch to replay or weakening the C or contract.

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

- Establish the typed execution-region boundary before migrating more loop,
  branch, or scope shapes. Do not encode region completion with a synthetic C
  sentinel, source-statement indices, or mutable completed-region sets.
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
- Measure each migration chunk at the exact fallback it intends to delete and
  retain a source-expansion-reverification canary for the same shape. A green
  general suite does not compensate for an ambiguous or mislabeled ownership
  assertion.

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

### Scoped population agreement

Open and close an allocation-bearing composite before an opaque call that has
failure and allocation-replacing success outcomes. Assert that the completed
Proof and fresh kernel certification agree on live allocations, retired
allocations, and every counted composite population. The failure outcome keeps
the original allocation; the success outcome retires it and retains only the
returned allocation. Expansion and deliberately corrupted explicit source
must pass and fail through the same Proof-owned transitions.

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
- A typed execution-region boundary composes through nested branches and loops;
  no semantic completion decision depends on a synthetic sentinel or replay
  `completed_branch_regions` bookkeeping.
- Closing an allocation-bearing composite before an opaque retiring call
  produces exactly the live/retired allocation sets and counted populations
  produced by fresh kernel certification on every outcome.
- Multi-size regressions satisfy the repository's verification-efficiency
  contract, and `scripts/check.sh` is green.
- User and internal documentation describes checked `Proof` transitions and
  verified expansion rather than ordinary certificate replay.
- This file and its Open-list line are deleted when the parallel replay model,
  its obsolete adapters, regressions, and documentation are complete.
