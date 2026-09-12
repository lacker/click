# Make `step` simple across a call precondition

## Status

P2. Phase 0 identity contract frozen and independently reviewed. Phase 1 is
ready to implement on a dedicated integration branch.

The kernel no longer contains a production proposition prover. The target
defect is unretained prerequisite derivation during simple call/statement
checking: `StatementPrerequisitePolicy::Planning` can derive a missing call
prerequisite while checking `step()`. The derivation is checked and therefore
sound, but it is not retained in the proof. `click expand` prints a bare
`step()`, and the expanded proof succeeds only because verification repeats the
same hidden planning. `Planning` also participates in other execution flows;
Phase 3 must census and classify those uses rather than treating this as one
isolated branch.

The goal is to remove that route. A simple `step()` must use an exactly stated
prerequisite or return a structured unmet requirement. A smart caller such as
`execute()` or `execute_until()` may respond by inserting an ordinary checked
`have` before retrying the same step. Expansion must expose the complete proof,
and the expansion must verify cold without hidden prerequisite search.

## Current foundation

The following mechanisms are already available and should be reused:

- unmet call prerequisites carry a structured `UnresolvedRequirement`,
  including the exact kernel proposition, context, lowering introductions, and
  callee-side source metadata;
- `Proof::try_statement_step_with_retries` can open, close, retain, and join a
  checked `have`, then retry the original statement step transactionally;
- source-backed retry validates the current call, selected interface, callee,
  source requirement, arguments, and memory snapshot before construction;
- registry and synthesized Surface spellings are admitted through one bounded,
  registry-first two-candidate path, and each candidate must lower back to the
  exact alpha/canonical-load identity of the reported requirement;
- checked `Have`, `Choose`, `Witness`, `Both`, `Intro`, `TransportUsing`, and
  coverage/simplification operations already exist and render as ordinary
  Surface Click;
- `ChosenProjection` retains bounded source leaves and validates the selected
  requirement, binder, and entry snapshot;
- unit-level synthesis covers static objects, quantified ranges, symbolic
  external ranges, and the generated one-byte `strlen` range; this does not yet
  establish a production retained proof; and
- wrong-epoch, invalidated-transport, permission, alpha-capture, and exact
  carrier-authorization regressions already guard important boundaries.

This is useful infrastructure, not evidence that final cutover is mechanical.
Dynamic C-string expansion still emits bare steps, and the two real
load-equation examples still lack faithful source presentation.

## Remaining architectural problem

Explicit proof construction needs the identity of the source item it is going
to name. Two different identities are currently lost.

### Caller requirement used by `choose`

The call carrier identifies the callee/interface, callee requirement ordinal,
source-registry ordinal, call arguments, and call snapshot. It does not
identify the caller requirement whose existential witness and entry facts
should be projected by `Choose`.

`Choose` intentionally selects a caller requirement declaration by ordinal.
That ordinal cannot be recovered from the callee ordinal. Nor may retry scan
`execution_start_facts`: that collection also contains guards, resources,
population facts, and derived entry facts, and a first structural match is
ambiguous and non-scalable.

The dynamic C-string vertical probe needs this exact source selection. Its
generated callee obligation is an existential containing an
addition-definedness guard and a quantified one-byte loadability claim. In the
target fixture, a covering range is a leaf of the caller's entry-snapshot
`cstr_readable(...)` requirement. The probe must validate that exact source
declaration and ordinal; it may not assume this relationship for every
similarly shaped proposition. Once the caller requirement is selected, the
ordinary `Choose`, `Witness`, transport, and coverage operations appear
sufficient; source selection is the missing input to test.

### Source access that produced a generated load

The remaining `bounded-pool` and `owned-string` obligations include a defining
equation of the form:

```text
Var(load_variable) == load(snapshot, pointer)
```

`GeneratedLoadBinding` preserves the semantic load identity: variable,
snapshot, pointer, and canonical load. It does not preserve the source
`Field`, `UnionField`, or `Index` occurrence that can spell the right-hand side
in Surface Click. That source form is erased before `mint_load_variable`.

Inferring it later from a pointer, hash, internal variable, or scan of lowered
propositions is ambiguous. Source occurrence provenance must cross the
source-to-generated-load lowering seam as presentation metadata.

## Design direction

Implement two explicit metadata layers:

1. a proof-local caller-requirement index in `ExecutionProofConstants`, built
   after the current function's entry requirements have been lowered.
2. source-to-load lowering metadata that identifies C access occurrences
   before expression lowering erases them.

The caller index may reuse source declarations from the file-scoped
`FunctionSourceRegistry`, but remains a separate proof-context-scoped index.
The load layer needs C-source ownership that registry does not currently
provide. Phase 0 must decide whether both use a generalized source-owner table
or separate persistent tables joined by a common owner ID. Do not force them
into one registry without a concrete lifecycle need.

The lifetimes are distinct: caller source declarations are file-scoped, the
caller index is proof-context-scoped, load occurrence IDs are source-scoped,
and generated-load provenance is transition-scoped.

The exact private names may differ, but the layers need typed identities
equivalent to:

```text
RequirementSourceId = (caller source owner, outer requirement ordinal)
LoadSourceId = (C source owner, source region, source access occurrence)
```

A shared `SourceOwnerId` is optional until Phase 0 proves it represents both
lifetimes without conflating them.

These identities are metadata, not propositions or proof authority. They may
select a source record that a checked operation names; they cannot make a fact
available, equate snapshots, choose a logical branch, or discharge a goal.

Required properties:

- IDs are minted deterministically from canonical declaration/source paths,
  before the relevant source distinctions are erased. C access occurrences
  require an explicit C-source owner table if the existing Click-only registry
  cannot own them; incidental registry insertion order is not identity.
- IDs name declarations or access occurrences. Actual arguments, binder
  substitutions, and memory snapshots are separate per-use instantiation data.
- Persistent proof branches share immutable owner tables and indexes rather
  than cloning complete environments.
- Lookup uses shallow stable keys and bounded candidate buckets. It never uses
  a deep structural expression as a hot map key or scans unrelated facts,
  requirements, functions, or memory history.
- A selected record is revalidated exactly. Missing, duplicate, stale,
  wrong-owner, wrong-argument, or wrong-epoch provenance fails closed.
- Source metadata stays out of proposition meaning, proof-obligation identity,
  contract-interface equality, and ordinary certificate serialization unless
  Phase 0 demonstrates a sound reason otherwise.
- Expanded proofs contain only ordinary Surface operations and spellings.
  Cold re-verification does not consult source IDs as proof authority.

### Caller-requirement path

Build an immutable caller-requirement index while establishing the initial
claim context and store it in shared execution-proof constants. The frozen
selection boundary is:

```text
lookup_unique_caller_requirement(
    owner, predicate_name, predicate_argument_slot, caller_parameter_slot,
    source_arguments, expected_entry_snapshot
) -> Option<CallerRequirementSelection>
```

The current statement index, scope, callee/interface, and callee requirement
ordinal remain in the retry's call-use validation envelope. They are checked
before this lookup but are not caller-index keys: one entry requirement may
legitimately support several call sites. Phase 1 accepts only an ordinary
caller function, a direct concrete call, and a top-level predicate requirement
whose selected argument is a direct caller parameter. Other owners and
argument shapes fail closed until a later phase gives them explicit identity.
The lookup key comes from the exact callee source clause already selected by
the unresolved carrier: resolve its source ordinal through the ordinary
function registry, require a top-level predicate call, substitute the checked
call arguments, then map its selected direct variable argument to the caller's
parsed parameter ordinal. This is direct indexed source access, not recovery
from the generated kernel obligation or a scan of caller requirements.

The result keeps three identities separate: the outer source declaration
ordinal, the lowered requirement-fact index, and the source token retained by
projection. It also contains exact source arguments for collision validation
and source presentation. None of the three positions may be substituted for
another. Phase 1 indexes only top-level predicate requirements; labels are
unwrapped while resources, generated definedness facts, and nested predicate
occurrences are rejected unless Phase 0 represents them explicitly. The outer
`RequirementSourceId` must survive predicate unfolding and definedness
lowering into `ChosenProjection`; derived facts do not replace that identity.

The index uses a shallow owner/predicate/argument-slot/parameter-slot key and
candidate buckets bounded at eight records. Exact expressions may be retained
for collision validation, but not used as an unbounded selection index.
Repeated equal-looking requirements at different ordinals remain
separate records, but a query that does not itself name one of those source IDs
must reject multiple exact matches as ambiguous. The nonzero-ordinal vertical
probe places a differently keyed unrelated requirement before the target; it
does not rely on selecting one of two otherwise identical declarations.

The selected record supplies the caller declaration ordinal and exact source
presentation. `Choose` remains the authority: it revalidates that ordinal and
fact, performs the binder substitution, and retains the projection. The
certificate continues to contain an ordinary `Choose` by ordinal or label.
Do not add a caller ordinal to the kernel `CallRequirementSource` unless the
vertical probe proves the proof-local mapping cannot be made sound.

### Generated-load path

Mint a `LoadSourceId` before source access form is erased. A parallel source
plan enters `certified_statement_transitions`, follows the evaluated expression
tree through `read_c_lvalue_expression_paths` to
`memory_loads::mint_load_variable`, and returns producer events on the
ephemeral execution-path results. Carry the ID on each event before bindings
are aggregated, then record:

```text
Variable -> Unique(exact GeneratedLoadBinding, LoadSourceId) | Ambiguous
```

The shallow variable is the map key; the complete binding is validation data,
not a deep hot-path key. Keep `GeneratedLoadBinding` source-independent. A
presentation consumer may retrieve a source spelling only after validating the
exact variable, pointer, canonical load, and snapshot. Equivalent generated
bindings from different source occurrences become ambiguous rather than
selecting the first.

The sidecar is transition-local proof metadata backed by persistent maps. It
must define fork sharing, output-sized delta updates, conflict/ambiguity
tombstones at joins, and rollback on a failed retry. A post-aggregation map
keyed only by variable or `GeneratedLoadBinding` is too late to recover which
source occurrence produced an ambiguous binding.

Source plans and events are explicit parameters/results, never thread-local or
global observers. Do not put source syntax or IDs into `CExpression`, kernel
proposition equality, `GeneratedLoadBinding`, contract identity, or ordinary
certificate serialization.

## Primary code touch points

| Concern | Current starting point |
| --- | --- |
| Click requirement sources | `src/surface/source_registry.rs`: `FunctionSourceRegistry` |
| Proof-local shared metadata | `ExecutionProofConstants` and initial claim construction |
| Caller selection | `ProofFactSource::Requirement`, `ChosenProjection`, and `apply_fixed_state_choose` |
| Retained retry | `smart_closures.rs`: `try_statement_step_with_retries` and source-backed admission |
| Semantic generated loads | `GeneratedLoadBinding` and the persistent generated-load maps |
| Source-erasure seam | `read_c_lvalue_expression_paths` to `memory_loads::mint_load_variable` |
| Final policy boundary | `transition_certification.rs` plus the refreshed `Planning`/`Contextual` census |

## Implementation plan

Work proceeds through two vertical landings, followed by orchestration and
cutover. A helper that has no production consumer does not land on master.

### Phase 0 — frozen identity contract

The following contract is the implementation boundary. The two identity
domains are deliberately separate even if a later refactor gives both a common
source-unit component.

Caller-side types, with private Rust names allowed to vary:

```text
CallerSourceOwnerId =
    (OrdinaryFunction, canonical source unit, declaration name)
RequirementSourceId = (CallerSourceOwnerId, outer requirement ordinal)
CallerRequirementKey =
    (predicate name, predicate argument slot, caller parameter slot)
RequirementFactRole = Principal(bounded unfolding path) | LoweringGuard(ordinal)
EntryFactOrigin = Requirement(RequirementSourceId, RequirementFactRole) | Derived
CallerRequirementRecord = {
    source ID, source proposition, shallow key,
    principal lowered fact index and exact fact,
    source arguments, entry snapshot
}
CallerRequirementSelection = {
    source ID, principal lowered fact index and exact fact,
    source proposition, source arguments, entry snapshot
}
ProjectionSourceToken = (RequirementSourceId, bounded connective path)
```

`initial_claim_context` must construct entry facts with a parallel
`EntryFactOrigin` stream. Requirement lowering, structural unfolding,
definedness replacement, and derived-fact insertion preserve or explicitly
replace those tags; the implementation never rediscovers them by comparing or
slicing the final proposition vector. Once final entry order is known, one
linear pass builds the proof-local index and projects the propositions used by
existing consumers. An eligible record has exactly one principal fact;
generated definedness and resource/population facts remain `Derived` and cannot
stand in for it. Structural predicate unfolding updates the principal fact's
bounded unfolding path while preserving its `RequirementSourceId`; it never
promotes an unfolded leaf or generated guard to a new source declaration.

Verification threads the exact verified-source-map key already called
`source_path` into proof construction. Together with the ordinary-function
declaration name, that is `CallerSourceOwnerId`; the file-scoped registry gains
this owner input rather than inventing identity from insertion order or a
display-only name.

`ProofFactSource::Requirement` and labels continue to serialize the outer
source ordinal. `apply_fixed_state_choose` resolves that source ID through the
index, then separately checks the recorded fact index and proposition against
the active fixed-state view. `ChosenProjection` replaces its overloaded
`source_index` with the source ID, lowered fact index, and projection token.
Checked unfolding and binder substitution remain proof authority; the token
only preserves the exact source leaf for presentation.

The caller index uses a persistent map of shallow keys to at most eight
records. Build time is linear in entry records. Lookup is logarithmic in keys
plus at most eight exact comparisons of source ID, arguments, fact, and entry
snapshot. Overfull buckets, duplicate exact candidates, unsupported labels or
nested/resource/generated forms, a stale fact position, a mismatched
call-use envelope, or any missing provenance fails with the original unmet
requirement. Direct concrete calls from ordinary caller proofs are the Phase 1
scope; callbacks, generic wrappers, and other caller-owner kinds remain a
fail-closed Phase 3 extension.

Load-side types:

```text
CSourceOwnerId =
    (canonical verified source unit, function declaration identity)
CSourceRegionId = source-layout statement index
LoadSourceId = (CSourceOwnerId, CSourceRegionId, access occurrence ordinal)
SourceLoadSite = (LoadSourceId, retained C0 source expression)
SourceLoadUse = {
    LoadSourceId, statement-entry SnapshotSelector,
    expected CMemorySnapshotIdentity, instantiated Surface C expression
}
GeneratedLoadSourceEvent = (exact GeneratedLoadBinding, SourceLoadUse)
GeneratedLoadSourceResolution =
    Unique(exact GeneratedLoadBinding, SourceLoadUse) | Ambiguous(variable)
```

Build an immutable source-load table and a statement/expression plan from the
parsed C0 tree before `to_kernel_expression` erases `Field`, `UnionField`,
`Index`, `Load`, and `SequentialRead`. Owners are ordered by canonical source
unit and declaration identity, regions reuse `SourceExecutionLayout` statement
indices, and occurrences use a documented preorder child traversal. Loop
iterations reuse the source ID; the binding's snapshot distinguishes uses.

The source plan is a parallel tree, not a map keyed by a deep expression path.
Alignment is created atomically: recursive C0 lowering returns
`LoweredExpressionWithSources { expression, plan }` and
`LoweredStatementWithSources { statement, plan }` (names illustrative), and
`AnnotationLowerer::lower_statement` composes both members in the same match
arm. `For` expansion, annotation checks, lowered calls/statement expressions,
and every other shape-changing rewrite create explicit synthetic `None` plan
nodes at the moment they create the kernel node. A separately reconstructed
preorder plan is forbidden.

The annotated-function result exposes the kernel function and its immutable
owner-tagged source plan/table separately; only the kernel function enters
semantic contract/theorem identity. Surface execution passes the current
statement plan explicitly into `certified_statement_transitions`. Kernel
expression evaluation carries the matching child plan and appends an event at
the same producer operation that mints the exact `GeneratedLoadBinding`.
Ephemeral expression, argument, statement, and function paths carry the event
vector to the certified transition. Every evaluated node consumes exactly its
aligned plan node; missing, duplicate, or out-of-order consumption fails
closed. Unsupported or synthetic expressions cannot later acquire provenance
by inference.

Surface execution forms `SourceLoadUse` from the immutable site plus the exact
recorded statement-entry selector and memory identity before entering the
kernel. Its instantiated Surface expression retains the written identifiers
but no mutable `CState`. The producer checks that the plan node corresponds to
the evaluated source access and returns it with the exact binding. A later
consumer must still resolve the selector to a recorded state with the expected
memory identity and re-lower the spelling there; a missing or overwritten loop
snapshot therefore fails closed instead of guessing from the current state.

Only an accepted checked transition updates proof presentation. Presentation
stores a persistent `Variable -> GeneratedLoadSourceResolution` map and an
append-only event sequence. The first exact binding/source pair is unique; the
same pair is idempotent; a different binding or source for that variable makes
a permanent ambiguity tombstone. Forks share roots, joins consume only each
arm's suffix since the parent, terminal outcomes retain path-local roots, and a
failed retry records nothing. The existing source-independent generated-load
map remains unchanged.

The active execution context carries the same `CSourceOwnerId` as its source
plan. Every transition, event recorder, join, terminal-outcome view, and
consumer checks that owner before accepting a site. Derived contexts that
still execute the same function share the owner-tagged table; a context that
changes the executing function must construct new constants and cannot reuse a
valid-looking ID from the old table.

A consumer queries by variable, requires a unique resolution, validates every
field of the exact binding, resolves the source ID in the current function's
immutable table, checks the retained and instantiated source forms agree,
resolves the recorded selector to the expected snapshot, re-lowers the Surface
expression there, and requires the exact defining equation. Missing/wrong
owners, regions, occurrences, pointers, loads, snapshots, selectors, event
ancestry, or source spellings fail closed. No pointer/name/hash heuristic or
ambient scan is an alternate route.

Both layers are presentation/planning metadata. Their IDs, tables, tags,
events, and resolutions do not participate in `CExpression`, `Proposition`,
`GeneratedLoadBinding`, contract, theorem, or certificate semantic equality,
hashing, ordering, or serialization. Expanded proofs contain only ordinary
Surface operations.

Each corresponding vertical landing includes deterministic tests at four
sizes; the tests and implementation land with their first production consumer:

- caller index sizes 1, 8, 64, and 512: linear construction, logarithmic
  shallow lookup, at most eight candidate validations, plus duplicate and
  overfull ambiguity cases; and
- load event sizes 8, 32, 128, and 512: logarithmic persistent updates and
  lookup, output-sized suffix joins, root sharing, rollback, and permanent
  conflict tombstones; include synthetic-node alignment and branch-plan
  mismatch cases.

Root owns both interfaces and the eventual retry/cutover wiring. Luna work may
implement a bounded layer only after these inputs are fixed; independent Luna
review must check snapshot authority and scaling before each vertical landing.

### Phase 1 — caller identity through one dynamic proof

Use one integration branch. Master receives this phase only when the complete
vertical behavior is green.

Root first commits the tagged-entry/index/selection interfaces on the Phase 1
integration branch. A Luna branch based on that exact commit implements only
the bounded index and its unit/scaling tests. Root integrates it and wires the
retry state machine and `ChosenProjection`; a separate Luna task may implement
only the explicit-`have` composition after that interface is fixed. Nothing
reaches master until the whole vertical behavior is green. An independent Luna
review audits the combined commit for ambiguity, snapshots,
expansion/deletion, and scaling.

Required vertical evidence:

- production C remains unchanged;
- a focused `cstr_source_identity_reordered_requirement` mdtest keeps the C
  body unchanged while proof-side contract variants place the relevant caller
  requirement at a nonzero ordinal and use an alternate pointer name;
- that regression also places unrelated guard/resource/derived entry facts
  before the requirement, asserts that the lowered fact-vector index still
  names that exact nonzero source declaration, and checks that `Choose`
  retains the expected projection;
- `cstr_dynamic_loadability` and `cstr_dynamic_indexed_read` expand with a
  retained `have` containing checked `Choose`, `Witness`, explicit transport,
  and coverage operations;
- expansion verifies in a fresh process, and an in-process direct-policy check
  or test-only counter proves that the logical Planning derivation leg was not
  entered; do not add a user-visible verification mode for this assertion;
- duplicate plausible requirements, wrong arguments, wrong source/binder
  mappings, wrong epochs, intervening invalidation, missing permission, and
  deletion of the transport or required `have` fail, while legitimate
  alpha-renamed binders still pass; and
- unrelated requirements do not change candidate count or asymptotic work.

Keep the existing dynamic boundary fixtures in the acceptance set, including
`cstr_dynamic_choose_extract`,
`cstr_dynamic_choose_extract_wrong_epoch`,
`cstr_dynamic_choose_extract_missing_transport`,
`cstr_dynamic_invalidated_transport`, and
`cstr_dynamic_indexed_read_requires_permission`.

### Phase 2 — load identity through real load equations

Continue on a fresh integration branch based on the landed Phase 1 result.

Root first commits the atomic lowering/plan and ephemeral evaluator-event
interfaces on the Phase 2 integration branch, including explicit file/API
ownership. A Luna branch based on that commit owns only source-occurrence
propagation and scaling tests. After root integrates it, a second Luna task
owns only the Surface sidecar/synthesis consumer and reduced real obligations.
Root owns generated-binding integration and retry interactions. Nothing reaches
master until the whole vertical behavior is green. An independent Luna review
checks ambiguity, epochs, source spelling, cold expansion, and scaling on the
combined candidate.

Required vertical evidence:

- one unchanged real obligation from each example maps source occurrence to
  exact generated binding and produces a faithful load-defining equation;
- the equation parses and lowers to the exact reported proposition at the
  correct memory point;
- its retained ordinary `have` expands and verifies cold;
- identical-looking accesses at different locations, conflicting source
  occurrences, stale provenance, and the same access at another epoch fail
  closed; and
- no internal load variable or inferred pointer hash is printed as source.

### Phase 3 — general retained-requirement orchestration

Root owns this serial phase because it changes the retry state machine and
smart execution routing.

1. Re-run the current hidden-Planning census on the integration base; do not
   rely on a historical fixture count.
2. Route supported requirements through the two source-identity paths and the
   existing exact/synthesis mechanisms.
3. Cover `call_precondition_disjunction_is_an_obligation` and its
   `rejects_neither_arm` negative, then sequential and multi-requirement calls,
   selected contracts/callbacks, branches, `execute_until`, scoped execution,
   and ordinary explicit `step` behavior. The minimal disjunction regression
   must show that bare `step()` returns the structured obligation without
   entering logical Planning.
4. Require every smart success to retain an ordinary proof; unsupported shapes
   must fail promptly with the original structured requirement.

### Phase 4 — remove hidden planning

Only after Phases 1--3 are green on one base:

1. Census every `StatementPrerequisitePolicy::Planning` logical derivation and
   every hidden logical derivation reachable through `Contextual` handling.
2. Preserve legitimate exact condition evaluation and explicit transport,
   including contextual checks that do not perform proposition search, while
   removing unretained logical derivation from simple call checking.
3. Verify that explicit `step()` either finds an exact prerequisite or returns
   the structured refusal, and that only smart callers construct proofs.
4. Expand and cold-reverify the complete current affected corpus.
5. Run unfiltered `scripts/check.sh` with the body-rerun census at zero.

Root owns the cutover and merge. A Luna reviewer performs an authority-boundary
audit on the exact green commit before it reaches master.

Issue-specific integration rule: root owns shared identities, the retry state
machine, and final cutover. Delegated implementation has nonoverlapping
ownership and frozen inputs; delegated review is read-only. Master advances
only at a complete vertical checkpoint with a production consumer,
regressions, independent review, and unpiped `scripts/check.sh` success. The
repository-wide worktree and integration rules remain in `AGENTS.md`.

## Final acceptance

- A bare call `step()` performs no unretained logical prerequisite derivation
  or Planning search; legitimate exact execution and checked condition routes
  remain.
- Smart execution retains every constructed prerequisite proof as an ordinary
  `have` before the owning call.
- Expansion exposes all witnesses, branches, transports, rewrites, and
  simplifications needed by the proof and verifies cold through the ordinary
  entry point.
- Deleting a necessary generated `have` or transport fails in minimal
  regressions.
- Caller requirements and source loads are selected by exact, typed,
  fail-closed provenance without ambient scans or semantic source heuristics.
- Wrong owner, argument, source/binder mapping, source occurrence, or memory
  epoch cannot authorize a proof; alpha-renamed binder names remain valid.
- The production C remains unchanged.
- The refreshed affected corpus, including dynamic C-string behavior and the
  two real load-equation examples, verifies with no hidden prerequisite
  derivation.
- Verification work remains approximately linear, up to indexed lookup
  factors, in source and certificate size.
- Unfiltered `scripts/check.sh` passes and both fixture harnesses report zero
  body reruns.

## Stop and revise if

- provenance requires ambient scans, display names, pointer/hash inference,
  first-match selection, deep hot-path keys, merged epochs, or metadata that
  grants facts or changes proposition meaning;
- the unchanged C cannot be proved by a rendered, cold-verifying sequence of
  ordinary Surface operations without a new semantic kernel rule; or
- verification becomes unexpectedly slow, produces an unverifiable
  certificate, or expansion disagrees with ordinary verification.

## Not in scope

- recursive-call `decreases` obligations;
- general completeness of smart proof search;
- new trusted proof rules or proof-step syntax merely to recover source
  identity; and
- changes to verified C that exist only to make a proof easier.
