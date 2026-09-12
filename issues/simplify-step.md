# Make `step` simple across a call precondition

## Status

P2. This is what remains of the 2026-09 kernel-search cleanup, whose other
work has landed: the kernel contains no production proposition prover, the
logical search lives in `src/surface/planning/proposition_search.rs`, and
every other kernel consumer decides by exact routes or emits an obligation
(see the kernel authority boundary in
[proof-objects.md](../docs/internals/proof-objects.md)). One route is left.

Implementation is paused as of 2026-09-12. The 2026-09-11 plan correctly
identified many local proof-construction requirements, but its premise that no
verification architecture was missing is no longer supported. Two independent
end-to-end attempts grew into 300--400 line C-string-specific prototypes and
still could not produce a retained explicit proof. Both were discarded before
merge. The common blocker is loss of exact source identity: the explicit proof
builder cannot identify the caller requirement to project with `choose`, and a
generated kernel load no longer identifies the source access that can spell its
defining equation.

Do not resume the package/delegation plan preserved at the end of this issue.
The authoritative next step is the bounded source-identity redesign below.
Keep the current hidden `Planning` compatibility path until both identity kinds
have been demonstrated by vertical, retained-proof regressions. Do not add more
C-string matchers, hardcoded source names, ambient-fact scans, or
proposition-shape heuristics to bridge the gap.

## Violated invariant

A simple tactic requests one deterministic checked operation and does no
search. `step()` over a call is classified simple, but when the callee's
precondition is not exactly available at the call, the step driver
discharges it by search: `StatementPrerequisitePolicy::Planning` in
`src/surface/proof/execution_planning/transition_certification.rs` asks
the planner for a derivation and checks it before accepting. The check
makes this sound. It is still search inside a simple step, and its success
leaves no trace: no `have` enters the proof, `click expand` prints a bare
`step()`, and the expansion re-verifies only because the same search runs
again on re-check. Every other smart success expands to explicit Surface
Click; this one does not.

The kernel side is already done: `prepare_verified_function_call` emits a
requirement the exact routes miss as `ProofObligation::verification_condition`
with the context `"<callee> precondition"` and the lowering-provenance
chain that `intro` consumes. The obligation-reporting gap described here is on
the surface: the emitted requirement is discharged as a prerequisite instead
of being presented as a goal the proof states. Later work exposed a separate
cross-layer provenance gap for naming the source requirements and loads used
to construct that explicit proof.

## Intended design

An emitted requirement becomes an ordinary goal closed before the step.

- The step driver reports an unresolved requirement as structured data
  (proposition, context, provenance chain) rather than discharging it.
- The smart planner synthesizes the requirement's Surface spelling, applies
  a real `have <requirement> by { ... }` operation on the `Proof` before the
  step, closes its body with checked steps, and retains it, so expansion
  prints the `have` and a certificate without it is rejected. The `have`'s
  goal must be the reported proposition up to alpha-equivalence (binder
  identity and `Exists` name blind, exact otherwise), since contract
  lowering and fixed-state lowering allocate binders from different ranges.
- An explicit proof states the requirement with `have` or `assumption`
  before the step; the exact route then discharges it and no obligation is
  raised. This already works today and is the manual escape hatch.
- The `Planning` leg is deleted. `step()` over a call is then simple: exact
  routes only.

## What has been established

Two early attempts built the mechanism and measured what it closes. Those
prototype branches were not merged; several independently reviewed components
described below subsequently landed as green commits. The prototypes remain
historical evidence, not implementation sources to copy.

**Reporting the requirement.** In `transition_certification.rs`, the
`Contextual` arm's checked-derivation leg is gated on
`obligation.is_assumable()`, so a required verification condition gets no
derivation leg. The refusal carries a structured payload,
`UnresolvedRequirement { proposition, context, introductions }`, on
`ClickError` (a private field with an accessor), built from the obligation
itself: its proposition, its context label such as `"strlen precondition"`,
and the package 17 chain from `ProofObligation::introductions()`. The
payload must survive unmodified up to `apply_step(ProofStep::Step)`; the
step drivers re-wrap errors on the way up and each re-wrap must forward it.

**Planning the `have`.** `Proof::step_discharging_reported_requirements`
wraps the statement step. On a reported requirement it synthesizes the
written form under a `QualifiedSynthesisScope`, `begin_have`s it, requires
the scope's goal to match the reported proposition (see the comparison
below), installs the obligation's chain with a new
`ProofScope::with_recorded_goal_introductions` so `intro` consumes the
recorded chain rather than one re-lowered from the synthesized text, closes
the body with the shared smart-closure vocabulary, and `join`s, which
retains an ordinary `ProofStep::Have` ahead of the `Step`. The loop is
bounded structurally: each planned `have` must discharge a requirement not
already discharged, so it is limited by the statement's distinct
obligations. `ConstructionEvidence::CertifiedStatementStep` in
`surface_construction.rs` is never reached for a smart `execute()`, because
the smart step planner applies `ProofStep::Step` directly; the `have` has
to be a real proof operation, not rendered evidence.

**One goal for construction and discharge.** A freshly lowered `have`
never compares equal to the kernel's requirement under derived
`PartialEq`: contract lowering allocates quantifier binders from 3,100,000
and fixed-state lowering from 2,000,000, and `Exists` includes its binder
name in equality while synthesis names binders `__click_qN`. The retained
answer is `propositions_are_alpha_equal`: `Exists` and `ForAll` compare
sorts, freshen both bodies to one variable, and recurse, ignoring the
binder name; `And`/`Or`/`Implies`/`Not` recurse; every other pair is exact
equality. It is deliberately stricter than the older
`propositions_alpha_equivalent`, which also canonicalizes loads. Load
naming is handled separately by `proposition_in_canonical_load_form`,
applied to both sides first, because contract lowering spells a load out
where `have` lowering names it. The planner accepts a `have` by that
comparison and the kernel discharges by the same one:
`PureFactContext::states_required_goal` takes condition leaves through the
exact indexed route and compares a quantified leaf against the quantified
facts alone, so unrelated facts are never visited. Unit tests to keep:
binder identity ignored; existential binder name ignored; binders
introduced under every connective; a differing non-binder subterm
rejected; a free-variable capture rejected; a differing quantifier
rejected.

**Presentation fixes that were needed.** `Exists` synthesis recovers the
binder name the contract wrote instead of generating `__click_qN`; `intro`
keys a universal's binding by the name the written body mentions rather
than the recorded chain's, so a proof that restates a kernel-built goal in
its own words resolves its own binder; the named-range loadability
synthesizer also spells a range whose byte count folded to an element
count, reading the start from the base pointer's own index. When a kernel
conjunction the written form does not spell is split with `both`, and one
conjunct is the lowering's own definedness guard, the written form travels
with the other conjunct, so the arm below it can still be rendered; the
arm still owes exactly its kernel conjunct.

**Closing the planned body.** The shared smart vocabulary, plus: a kernel
conjunction the written form does not spell is split with `both`; an
existential names a witness from the call's own arguments, then zero, then
each of the caller's own existential requirements through `choose`; the
requirement is spelled literally, and failing that with its leading
definedness-guard conjuncts left to the lowering that regenerates them.

**Measured reach.** With the three prerequisites below landed, that
mechanism discharged seven of the twelve affected mdtests by a planned
`have`, plus the two hand-written spelling fixtures
(`static_local_array_requirement_stated_explicitly`,
`loadable_range_requirement_stated_explicitly`), which had relied on the
deleted leg for conjunction splitting. Body shapes seen: the static family
gets one `have` of the whole six-conjunct requirement closed by nested
`both`/`rewrite`/`normalize`; `forall_loadable_range` gets
`intro(); intro(); simp();`; `exists_loadable_range` gets `witness` plus
`both`. The `cstr` fixtures' universal requirement
`forall k. 0 <= k and k < len implies loadable(bytes[k..k + 1])` also
closes once the written form travels across the guard split.

**Prerequisites already on master.** Emitted requirements carry the
provenance chain; existential lowering places definedness guards under
their binder as body conjuncts, since an implication there would be
vacuously satisfiable; loads through foreign static objects and
`loadable(p[a..b])` ranges over an external argument synthesize and
round-trip.

**Additional green infrastructure landed during the 2026-09-12 campaign.**
These changes are useful independently and remain on master:

- exact alpha/canonical-load identity and indexed availability behavior;
- source-backed retry authorization and retained-`have` orchestration for the
  cases whose source identity is already available;
- explicit dynamic snapshot transport support and its wrong-epoch and
  invalidation regressions;
- static, multidimensional, quantified-range, symbolic external-range, and
  constant-one external-range synthesis, including the production `strlen`
  carrier shape;
- constructor disequality, retained algebraic orientation, and the relevant
  stack-safety repairs; and
- the exact two-candidate carrier-admission path landed in `9cfee80a`: after
  source/call authorization, try the registry spelling and at most one
  synthesized spelling, accepting either only after exact alpha/canonical-load
  re-lowering. Its callee/interface/argument/ordinal authorization negatives
  and the full repository gate pass.

The presence of these prerequisites must not be read as evidence that final
cutover is close. They remove local obstacles, but neither supplies the source
identity needed by the remaining dynamic and load-equation consumers.

## Remaining gaps

The historical census below identified twelve mdtests with automatic proofs
that relied on hidden discharge:
`cstr_dynamic_indexed_read`, `cstr_dynamic_indexed_read_requires_permission`,
`cstr_dynamic_loadability`, `stdlib_external_contracts`,
`exists_loadable_range`, `forall_loadable_range`, `file_scope_static_arrays`,
`static_array_parity_scalar`, `static_array_parity_multidimensional`,
`static_array_parity_fixed_multidimensional`, `static_local_arrays`,
`contract_refinement_uses_implied_requirement`, plus `examples/bounded-pool`
and `examples/owned-string`. Their C and their proofs stay as they are; the
planner must close them. Re-run this census on the restart base: several local
capabilities have since landed, so this list is an acceptance corpus, not a
claim that all fourteen inputs still fail for the same reason.

Two architectural identity gaps now dominate the remaining work:

1. **Exact caller-requirement identity.** The dynamic C-string obligation is
   an existential containing an addition-definedness guard and a quantified
   one-byte range:

   ```text
   exists len:CInt32 {
       !signed_add_overflows(len, 1) &&
       forall k:CInt32 {
           (0 <= k && k < len) => loadable((bytes + k)[0..1])
       }
   }
   ```

   This is the generated callee/read obligation, not the source declaration of
   `cstr_readable`. The caller source requirement is an existential whose body
   contains the entry covering leaf `loadable(bytes[0..len + 1])` together with
   its bounds, non-null, and terminator clauses. The current prelude declaration
   is authoritative; the redesign must preserve the identity connecting that
   source requirement to the generated obligation without conflating their
   proposition shapes.

   The covering `loadable(bytes[0..len + 1])` is an entry-snapshot leaf of a
   caller `cstr_readable(...)` requirement. `Choose` deliberately requires the
   exact caller declaration ordinal. The call-requirement carrier identifies
   the callee requirement, source registry entry, call arguments, and snapshot;
   it does not identify which caller requirement may be projected. Recovering
   that ordinal by scanning proof facts, choosing the first matching shape, or
   hardcoding `bytes` is ambiguous and violates the verification-efficiency
   contract.

2. **Exact generated-load source identity.** `examples/bounded-pool` and
   `examples/owned-string` raise requirements whose head conjunct is
   `Var(loadvar) == load(snapshot, p)`. By the time the kernel load variable is
   minted, the distinction between source `Field`, `UnionField`, and `Index`
   access occurrences has been erased. Pointer/hash inference from proof
   material would be ambiguous, and printing an internal load variable as a
   source identifier is invalid. Faithful synthesis therefore needs retained
   provenance for the originating source access, not another load-expression
   heuristic.

The witness/transport/coverage operations themselves are not known to be the
architectural gap. Once the exact caller requirement is selected, existing
checked `Choose`, `Witness`, `TransportUsing`, and coverage operations provide
the candidate vocabulary. The vertical probe must establish the exact checked
composition; it may not rename an entry snapshot to the current one or
transport a target without the source range and required frame evidence.
Likewise, the carrier-admission path can retain a faithful load equation once
its source access is nameable. The missing input in both cases is source
identity.

Also known: `auto` reports it has no explicit simple certificate for an
existential over `CInt32`, pre-existing; and a `both` on a guard conjunct
leaves a body below it unrenderable when the written form cannot travel
with either arm, the conjunct-guard record the normalization planner lacks.

Two additional local gaps found by the function-contracts campaign are now
closed and are not part of the redesign: checked disequality of distinct
algebraic constructors, and retained orientation of the relevant pure-function
equation across a call.

## Eventual intended regression

This is the final behavior after the redesign restart gates pass, not a current
implementation package.

`mdtests/call_precondition_disjunction_is_an_obligation.md` with
`by { execute(); simp(); }`: the expansion contains
`have x > 0 or y > 0 by { left(); }` before the step, re-verifies through
the ordinary entry point, and is rejected when that `have` is deleted. The
12 mdtests and two examples above verify unchanged and their expansions print the
discharging `have`. A requirement with a hidden guard in front of a written
implication introduces both in order through the chain. Requirement
checking is flat in unrelated caller facts.

## Eventual acceptance criteria

These criteria govern final completion after the bounded redesign and vertical
probes. They do not authorize immediate `Planning` removal.

- `StatementPrerequisitePolicy::Planning` and the checked-derivation leg in
  `transition_certification.rs` are deleted; `step()` discharges a call
  requirement by exact routes only.
- Every emitted call requirement in both fixture harnesses is closed by a
  retained `have` that expansion prints, or by an explicit one in the
  source; the 12 mdtests and two examples above verify with their
  current C and proof text.
- No new kernel rule, no new `ProofStep` variant, no grammar change, no
  ambient-fact scan in the planner.
- `scripts/check.sh` passes with the body-rerun census pinned at zero.

## Not in scope

Recursive-call `decreases` at a call site: the recursive-edge check is a
syntactic walk in `termination.rs`, not search, and emitting it as a call
obligation needs the caller's termination plan at the call site, which the
whole-program termination pass does not provide. The `arithmetic` smart
tactic is documented in the [arithmetic certificate reference](../docs/reference/tactics/index.md).

## 2026-09-12 bounded source-identity redesign

This section is authoritative for the next work on the issue. Its purpose is
to settle one coherent representation before implementation resumes. It is a
design phase, not authorization to land another chain of disconnected helper
commits.

### Decision

Introduce proof-local, immutable identities for source occurrences that must
survive lowering:

- a **requirement source identity** names one top-level caller requirement
  declaration and its source presentation; and
- a **load source identity** names one source memory-access occurrence whose
  lowering produced a generated load.

These identities are provenance, not propositions and not proof authority.
They may select the source object that an ordinary checked operation names,
but they cannot make an unavailable fact available, equate snapshots, choose a
logical branch, or discharge a requirement. Every generated proof must still
be accepted by the existing simple proof operations.

Use separate typed identities even if they share an internal numeric owner/key
representation. Do not overload a callee requirement ordinal, load variable,
pointer term, structural hash, display name, or proof-fact vector position as a
source identity. Memory epoch remains an independent semantic dimension; the
same load source occurrence at a different epoch does not become interchangeable.

### Required identity properties

The redesign must specify and test all of the following before implementation
packages are dispatched:

1. **Minting.** State exactly where each identity is allocated. A source
   occurrence is minted once by the owning parsed/lowered function context,
   not rediscovered during smart retry.
2. **Ownership.** Include enough owner identity that IDs from different
   functions, contracts, or instantiated callback contexts cannot collide.
3. **Propagation.** Provide a field-by-field lifecycle from source AST through
   C0/lowering, kernel terms or proof-local presentation records, obligations,
   proof facts/projections, synthesis, and expansion.
4. **Substitution and instantiation.** Define when an instantiated occurrence
   keeps its source ID and where its argument substitution is recorded. The ID
   names the occurrence; the substitution names this use of it.
5. **Persistence.** Copies and persistent proof siblings may share immutable
   source registries without cloning whole environments per function or tactic.
6. **Lookup.** Hot-path lookup is by shallow stable identity. It must not use
   linear exact-premise searches, deep structural map keys, or scans of all
   ambient facts. Exact structural comparison may validate a small selected
   record, never serve as an unbounded selection algorithm.
7. **Ambiguity.** Missing, stale, multiply applicable, wrong-owner, or
   wrong-snapshot identity is a prompt bounded refusal. Never choose the first
   plausible source.
8. **Semantic neutrality.** Document whether the metadata participates in
   equality, hashing, ordering, serialization, diagnostics, and certificate
   identity. Default to exclusion unless two values with different provenance
   must be kept distinct for sound downstream presentation. Any exception
   needs an explicit regression.
9. **Erasure.** A retained expanded proof contains ordinary source-level
   operations, not an opaque source-ID operation. Re-verification must not need
   the smart planner or a hidden provenance oracle.

### Architecture questions to resolve

Produce a short design record in this issue, with concrete type shapes and a
pipeline table, answering these questions:

- Is the common owner a parsed function, a validated function block, a kernel
  function instance, or an explicit immutable `ProofSourceRegistry`?
- How does a call's exact source-argument occurrence query the bounded set of
  relevant caller requirement IDs without structural fact scans?
- How does a requirement source identity pass through labels, resource and
  definedness wrappers, lowering-introduction records, `ChosenProjection`, the
  retained `Choose` certificate, and expansion without being confused with a
  proof-fact vector position?
- Does `Choose` continue to retain the declaration ordinal in its certificate
  while resolving it through a requirement source ID during construction?
- Where is a load source ID attached before C0 `Field`/`UnionField`/`Index`
  lowering erases the source form, and how does it reach
  `mint_load_variable`/registered-load presentation?
- How are callback instantiation, generic substitution, function inlining,
  repeated source accesses, and identical-looking accesses at different source
  locations distinguished?
- Which source table entry contains the exact Surface spelling and qualified
  scope required for round-trip lowering?
- How are source registries bounded and shared so explicit-simple projects
  remain approximately linear in input and certificate size?

Do not begin production implementation while any answer depends on "find the
matching proposition/load/pointer later." That is the implicit reconstruction
this redesign is meant to remove.

### Bounded vertical prototypes

After the type/lifecycle design is reviewed, implement two vertical probes on
one integration base. These probes are the feasibility test for the redesign;
they are not separate opportunities for special-case logic.

**Caller-requirement probe.** Keep the production C body unchanged. Use
proof-side/synthetic contract variants that place the relevant caller
requirement at a nonzero ordinal and use an alternate pointer parameter name.
The retained expansion must identify that exact source requirement, then
contain ordinary `Choose`, `Witness`, one or more explicit entry-to-current
`TransportUsing` and checked coverage steps, using only the bounded
compositions supported by the existing checker. It must verify in a fresh
process. Duplicate plausible caller requirements, a wrong argument,
wrong epoch, intervening invalidating write, or deletion of the transport must
fail. The implementation must contain no `cstr`-named matcher, hardcoded source
name, or ambient fact scan.

**Generated-load probe.** Reduce one unchanged real obligation from each of
`bounded-pool` and `owned-string`. A source identity must let synthesis spell
the actual originating access and memory point, round-trip to the exact load
equation, retain an ordinary `have`, and verify cold. Identical-looking accesses
at different source locations and the same access at a different memory epoch
must remain distinct. An unnameable or stale source identity must refuse rather
than emit an internal variable or infer from a pointer hash.

If either vertical probe requires a new trusted rule, new proof-step syntax,
whole-context scan, special-case source name, or unverifiable expansion, stop
and revise the identity design. Do not land only the latest local helper and
continue the previous workaround cascade.

### Restart gates

Implementation of the final planner and `Planning` removal resumes only when:

- the identity types, owners, minting points, and complete propagation table
  are written and independently reviewed;
- deterministic complexity bounds and at least four-size scaling regressions
  are specified for registry construction, lookup, cloning, and substitution;
- both vertical probes pass ordinary verification, expansion, deletion
  checks, and cold re-verification on the same green base;
- no probe contains a source-pattern special case or relies on hidden
  `Planning` after expansion; and
- the current `Planning`/`Contextual` census has been refreshed and every
  remaining consumer has an assigned exact or smart-construction replacement.

Until then, retain the compatibility path and keep master green. Design work
may update this issue and add minimal reductions in an isolated worktree, but
do not merge unused metadata, speculative carrier fields, or helpers without a
production consumer.

### Implementation after restart

Once the restart gates pass, use one coordinated vertical integration branch:

1. land the reviewed source registry and identity propagation as one coherent
   representation change with scaling tests;
2. make dynamic C-string and load-equation proof construction ordinary
   consumers of that representation, preserving exact carrier admission and
   checked proof operations;
3. expand and cold-reverify the full affected corpus, fixing only gaps that are
   expressible through the agreed general identity/operation interfaces;
4. refresh the policy census, route every smart consumer, and only then delete
   `StatementPrerequisitePolicy::Planning` and the remaining hidden
   `Contextual` derivation routes; and
5. run the complete acceptance matrix and unfiltered `scripts/check.sh` before
   deleting this issue.

Parallel agents may independently audit the identity lifecycle, scaling, and
expanded certificates. Do not split ownership of the identity representation,
retry state machine, or final policy cutover, and do not run competing
implementations of the same vertical probe.

## Superseded 2026-09-11 implementation and delegation plan

The remainder is preserved as historical detail and a source of regressions.
It is not the current dispatch plan. Where it conflicts with the bounded
source-identity redesign above, the redesign governs.

> **Historical only:** do not dispatch the packages, dependency order, or
> cutover below. Reuse individual regressions only after the redesign restart
> gates select and validate the replacement interfaces.

### Assessment and decision boundaries

The bulk of the work is known: report the obligation, restate it faithfully,
prove it through existing `Proof` operations, retain the `Have`, and make all
call-step consumers stop using hidden discharge. This is a coordinated tooling
change, not an open-ended search for a new verification architecture.

The difficult uncertainties are narrower:

1. Whether the two examples' load-defining equations can be round-tripped with
   the existing source/provenance maps and snapshot spellings.
2. Whether the dynamically quantified string requirements can be closed by a
   bounded composition of existing witness, transport, and coverage operations.
3. How much presentation metadata is needed to keep nested guard/conjunction
   proofs renderable when their written form differs from their kernel form.

These are early feasibility checkpoints, not work to discover after deleting
the fallback. Each must produce a checked, renderable regression before final
cutover. If a checkpoint exposes a missing simple operation or an unavoidable
new syntax requirement, report the exact proposition and the failed operation;
revisit this design before changing the language or trusted rules. Do not
silently turn an uncertainty into a new primitive or rewrite the C.

No fundamental change is intended to the kernel/surface authority boundary,
memory semantics, contract semantics, persistent proof object, or certificate
format. Internal structs, indexes, and presentation metadata may change.
Alpha-invariant identity is a representation facility, not permission to add
logical reasoning to the frozen atomic checkers. Existing `have`, `both`,
`intro`, `left`/`right`, `witness`, `choose`, `instantiate`, `rewrite`,
`normalize`, and explicit `transport` operations are the target vocabulary.
Smart `simp` may help construction, but its retained expansion must contain
checked simple operations as usual.

The earlier sections preserve the historical attempts' findings. Where this
plan tightens their suggestions, this plan governs the next implementation.
In particular, comparing against every quantified fact is not an acceptable
final implementation of exact requirement lookup.

### Observable behavior and invariants

For a caller with only `x > 0`, stepping a call requiring `x > 0 or y > 0`
must report an unmet precondition. Smart `execute()` must construct:

```click
have x > 0 or y > 0 by {
    left();
}
step();
```

This fragment concerns the call itself; declaration and return steps still
appear where the C requires them. The disjunction fixture must pin that the
selected arm is checked against the caller's premise. Do not assume a tactic
closes a branch merely because it selected it; retain any additional simple
closure the current checked `left` operation requires.

Keep these invariants at every accepted transition:

- A bare `step` either succeeds through its existing deterministic checked
  routes or returns a structured requirement. It never asks a smart planner
  for the missing proof. Explicit `step` callers receive the requirement;
  only a smart caller invokes the requirement planner.
- A failed attempted step publishes no execution successor, new call fact,
  consumed resource, changed frontier, or partially built certificate.
- The planner proves the requirement at the same frontier at which the step
  was refused. Callee postconditions and scratch execution successor facts
  are unavailable as premises for that proof.
- A requirement's Surface spelling lowers to that requirement under the
  precisely defined identity relation below. An easier-looking or merely
  implied proposition is not an acceptable substitute for the `have` goal.
- Presentation metadata cannot change the goal, grant facts, or prove a
  guard. The nested body still owes all of the kernel proposition.
- A completed `have` rejoins its exact parent through the ordinary scope
  API, publishes only its checked fact delta, and retains `ProofStep::Have`.
- Expansion attributes the inserted proof to the owning smart source site,
  places it before the call in the correct branch/scope, and re-verifies the
  rewritten source through the normal entry point.
- No required call condition may re-enter hidden derivation through a
  different prerequisite policy after `Planning` has been removed.

The compatibility target is the listed fixtures and examples, not arbitrary
completeness of automation. An unsupported new requirement should fail
promptly with its context and useful bounded proof information. Existing
explicit proofs that relied on hidden call search may need an explicit `have`;
do not reclassify `step` as smart to preserve that accidental behavior.

### Code map for the coordinator

Paths and symbols below were inspected at the design base. Recheck locations
on the eventual implementation base before assigning files.

| Responsibility | Starting points |
| --- | --- |
| Kernel call requirements and their provenance | `src/kernel/functions.rs`: `prepare_verified_function_call`; `src/kernel/reasoning/path_facts.rs`: `LoweringIntroductions`, `wrap_path_context_with_introductions`, `guard_quantified_witness` |
| Requirement dispatch and policy definitions | `src/surface/proof/execution_planning/transition_certification.rs`; `src/surface/proof/execution_planning/context.rs`: `StatementPrerequisitePolicy` |
| Error payload and diagnostic preservation | `src/surface.rs`: `ClickError`; `src/surface/proof/checked_drivers/statement_step.rs`; wrapping sites in `cursor_execution.rs` and checked drivers |
| Checked statement operation | `src/surface/proof/proof_object/execution_statements.rs`: `apply_execution_statement_step`; `checked_drivers/statement_step.rs`: `check_statement_step` |
| Smart execution entry points | `src/surface/proof/smart_execution.rs`: `try_linear_execute_descendant`, `try_linear_execute_until_descendant`; `proof_object/execution_statements.rs`: `apply_planned_smart_step` and execution fallbacks; `checked_drivers/proof_execution.rs` |
| Nested proof authority | `src/surface/proof/proof_object/splits_and_scopes.rs`: `begin_have`, `split_focused_both`; `proof_object/scope.rs`: `join`, `join_nested`; `proof_object/construction.rs`: `with_recorded_goal_introductions` |
| Written/kernel correspondence | `src/surface/proof/surface_synthesis.rs`, its `tests.rs`, `surface_construction.rs`, proposition presentation in the proof state, and introduction handling in `proof_object/fixed_state_steps.rs` |
| Existing load spelling | `surface_synthesis.rs`: `registered_load_in_state`, `synthesize_surface_equality_across_points`, qualified/entry/snapshot synthesis scopes |
| Goal identity and fact indexes | `src/kernel/api/contract_certification.rs`: existing `propositions_alpha_equivalent`; `src/kernel/assumptions.rs`, `assumptions/proposition_reasoning.rs`, `primitives.rs`: `PureFactContext`; `src/surface/proof/proof_object/fact_index.rs` |
| Checked smart closure and transport | `src/surface/proof/smart_closures.rs`; `smart_execution.rs`: `search_fixed_state_fact_transport`, `try_planned_execution_proposition_fact_transport`; explicit loadability transport planning |
| Regression entry points | `src/surface/tests/tactic_tests/statement_steps.rs`; `src/surface/proof/proof_object/tests.rs`; `tests/mdtests.rs`; `tests/examples.rs` |

`StatementPrerequisitePolicy::Planning` also controls condition transitions,
path filtering, fact transport, and scratch construction. Removing the enum
variant is not a mechanical replacement with `Contextual`. Census each use
and preserve the legitimate checked behavior through the appropriate smart or
simple operation. Conversely, the existing `Contextual` arm itself calls
`derive_proposition`; removing only the `Planning` arm leaves the bug alive.

### Shared contracts to agree before parallel implementation

The following names are proposed internal interfaces, not claims that these
symbols already exist. The coordinator owns the small shared declarations and
module wiring so workers do not independently invent incompatible APIs.

#### Structured requirement result

Use the previously established error-carrier approach: a private, shared
payload on `ClickError`, with an internal accessor and constructor/attachment
helper. Suggested semantic shape:

```text
UnresolvedRequirement {
    proposition: exact kernel Proposition,
    context: optional original obligation context,
    introductions: recorded LoweringIntroductions,
}
```

Store the potentially large payload behind `Arc` or another existing shared
owner. Ordinary errors should stay small. Do not put raw memory snapshots into
the rendered error, serialize the payload into a message and parse it later,
or expose a new public user-facing error format solely for the planner.

Construct it from the refused required verification condition before any
message-oriented rewriting. Preserve the original proposition, not an
unproved load-resolved approximation. The fact that exact checks may inspect
a canonical form must not replace the authoritative reported goal.

Retain both the obligation context and existing tactic/source attribution.
Each wrapper must forward the payload together with existing diagnostic,
search-failure, and timing information. Test the actual path through
`apply_step(ProofStep::Step)`, not merely a payload getter.
Prefer the existing `ClickError::with_context`/`with_prefix` machinery over
constructing a new error from `error.message()`. Update `Clone` and all
constructors consistently, and invalidate the rendered-message cache when
changing presentation. Keep the shared payload out of unbounded debug output.

Use `obligation.is_assumable()` to distinguish the historically different
obligation categories. The transitional design may leave existing handling of
assumable evaluator obligations intact while required verification conditions
are reported. Final review must account for every remaining derivation call:
the simple call route must not retain logical search under any category.
Do not rename a verification condition to an assumable obligation as a bypass.

The payload carries no authority to mutate a `Proof`. Its frontier identity is
the immutable proof on which the attempted step ran. If an adapter can return
a requirement from a different scratch frontier, it must return control to
that frontier's checked proof construction; it cannot attach the requirement
to an arbitrary ancestor.

#### Requirement identity and indexed availability

Define one named relation used by both the planned-`have` round-trip check and
the exact requirement-availability query. It consists of:

1. The existing, deterministic canonical load naming representation, applied
   consistently to both propositions. It must preserve distinct memory epochs
   and require no premise search or new frame inference.
2. Alpha-invariant structural identity: corresponding bound variables may be
   renamed, existential display names are ignored, sorts and quantifier kinds
   must match, and free variables and every other semantic subterm remain exact.

This is not implication, simplification, commutative matching, or arbitrary
snapshot equivalence. The older `propositions_alpha_equivalent` does more
load canonicalization internally; do not silently substitute it for the new
contract or broaden all its existing consumers as part of this work.

Implement comparison/key construction with a binder environment, for example
bound-variable positions, and a single structural walk. Avoid repeatedly
freshening/cloning the whole remaining body at each nested quantifier; that
can turn one deeply nested input into quadratic work. Reuse existing stable
term/memory identities rather than traversing complete memory histories.
Handle binders under every connective, nested shadowing, and all currently
supported sorts without conflating machine integers with mathematical ones.

Suggested exact query: `PureFactContext::states_required_goal(&Proposition)`.
Its allowed structural behavior is to find a stated fact under the identity
relation or assemble an explicit conjunction from already stated components.
Condition leaves use indexed exact routes. It must not choose an `Or` arm,
introduce an implication, instantiate a universal, or invent a witness.
Those are precisely the operations the planned `have` must record.

Use an alpha-invariant structural key/index for quantified facts rather than
scanning a quantified-fact bucket. Insertion can pay for the inserted fact's
own size. A query can pay for the queried proposition's size and indexed
access, with an exact collision check if a fingerprint is used. A coarse key
such as only the quantifier sort is insufficient. Keep the index persistent
and update it through the existing insertion, restriction, removal, and
context-sharing paths; stale restricted facts must never become available.

Construction and kernel availability must agree about conjunction leaves and
load naming. Add the query at the call requirement decision points, including
guard requirements, so a checked `have` prevents the same obligation from
being emitted again. Do not add propositional search to `PureFactContext::decide`
or the frozen atomic memory/resource checkers.

#### Surface synthesis and presentation

The synthesis worker returns a proposed ordinary `ClickProposition`; the
coordinator's planner owns `begin_have`, lowering, equivalence checking, and
publication. Synthesis success by itself is never a proof or a guarantee that
the expression names the correct snapshot.

Attempt literal synthesis under the frontier's `QualifiedSynthesisScope` and
the relevant recorded snapshot/entry context. A fallback may omit a leading
definedness-guard spelling only if normal lowering regenerates exactly that
guard and the complete lowered goal passes the identity check. No arbitrary
conjunct dropping, normalization to a weaker proposition, or special parser
mode is allowed.

Recover readable existential binder names from recorded written provenance
when available, with deterministic capture avoidance and a fresh-name fallback.
When introducing a universal, bind the name used by the current written body
to the variable introduced by the checked kernel operation. The recorded
contract's display name may differ. The introductions chain describes head
nodes, including hidden guards; it is not a substitute for the actual checked
goal structure.

Add a `ProofScope` presentation adapter for the existing
`Proof::with_recorded_goal_introductions`. Install the reported chain only
after matching the lowered `have` goal to the requirement. If recorded binder
identities need rebinding to the alpha-renamed goal, derive that mapping from
the checked correspondence; do not paste foreign binder IDs into a scope and
assume they resolve. Preserve the scope root, semantic state, and ancestry.

For conjunction splitting, keep written `And` children where they correspond
to the actual kernel children. Where lowering inserted a guard conjunction,
retain the written body on its corresponding semantic child and let the guard
child retain its own exact goal. Establish the correspondence from lowering
metadata or by lowering and exact comparison, never from the heuristic that
an inconvenient conjunct "looks like a guard". If existing head-chain metadata
cannot express the correspondence, add a narrowly scoped presentation record
produced alongside lowering. It is internal metadata, not a new proof rule.
If neither child can be rendered, return a bounded construction failure.

#### Checked requirement planner

Suggested entry point:
`Proof::step_discharging_reported_requirements` (internal smart planning only).
Conceptual algorithm:

```text
working := the current immutable Proof
attempted_requirements := an empty indexed set for this frontier
repeat under the owning smart tactic's existing budget:
    result := working.apply_step(Step)
    if a verification limit fired: propagate the limit failure
    if result succeeded: return its checked descendant
    if failure has no unresolved-requirement payload: propagate it
    requirement := payload from this exact failed attempt
    if this normalized requirement was already proved/tried here:
        fail locally with repeated-requirement diagnostic
    spelling := synthesize requirement at working's frontier
    scope := working.begin_have(spelling)
    require scope goal matches requirement under the shared identity
    attach the correctly rebound recorded presentation chain
    closed_scope := close using checked operations and selected premises
    require closed_scope is complete
    working := closed_scope.join()
    require the new stated fact is exactly available and frontier unchanged
```

Track a stable requirement identity under alpha-renaming and canonical load
naming; raw binder allocation numbers cannot defeat duplicate detection.
Reset the per-frontier set after a successful statement advance. Candidate
failure discards only the persistent candidate descendant; do not leave an
open `have` in the caller or manually splice a replacement proof node.

Distinct-obligation progress alone is not a complete work bound: rerunning a
large statement once for each newly exposed obligation can multiply its cost,
and lowering could mint fresh representations on each attempt. Charge all
attempts to the same smart budget, use stable identities, and test multi-
requirement calls. Do not reset the budget per `have`. If existing APIs make
discovery repeatedly re-execute an expensive prefix, consider a shared
statement-local preparation result; it must not become a second semantic
execution engine. The emitted explicit proof still checks one call step.

Use the shared smart closure vocabulary on the scope body and retain its
checked descendants. A raw `PropositionDerivation` can guide planning but
cannot replace a Surface proof or be smuggled into a `Step` certificate.
`ConstructionEvidence::CertifiedStatementStep` rendering is not the insertion
point: smart execution's direct checked path must own the real `Have`.

#### Local witness/transport/coverage planning

The planner input should include a small, typed collection of relevant
kernel/source premise pairs, their recorded snapshots, and call-argument
expressions. Build it from the selected call's arguments and relevant
recorded caller requirements using existing indexes. Do not materialize
`ProofFacts::to_vec()` or enumerate all ambient facts to construct this input.
If the needed reverse lookup does not exist, add and test a local index rather
than burying a whole-context scan in a helper.

Use a stable candidate order: compatible call-argument values, zero of the
correct sort, then witnesses obtained with `choose` from relevant recorded
existential caller requirements. Deduplicate candidates; introduce fresh
source names capture-free. Existential elimination must stay scoped so its
witness does not leak as an unconstrained caller fact.

For the dynamic string shape, the target sequence is:

1. Choose the relevant caller witness, if needed, and use it for the callee's
   existential with `witness`.
2. Split the actual body and prove its definedness/bounds guards.
3. Select the covering loadability fact at its recorded earlier snapshot.
4. Prove the needed preservation with the existing explicit transport operation
   and its named effect/frame premises. Transport the covering range, then
   prove target coverage; alternatively prove the target subrange at the source
   snapshot and transport that target when the existing operation requires it.
   Try these two bounded compositions, not arbitrary permutations of facts.
5. Close the resulting current-snapshot subrange goal with the existing
   checkable coverage certificate and join the nested scopes.

The earlier snapshot cannot simply be renamed to the current one. Include a
negative test where an intervening effect actually invalidates the relevant
permission. The retained certificate must contain the transport and its
premises. Expansion deleting a necessary transport must fail.

The existing concrete-witness mdtest is useful evidence for existential
presentation, but it does not by itself establish the dynamic snapshot
composition. Build that regression from the actual dynamic fixture's C,
without adding a proof-only C declaration or changing identifiers.

#### Load-defining equations

Reduce one real obligation from each of `bounded-pool` and `owned-string`
before implementing a generic rule. Preserve the exact load variable,
pointer type, offset, and memory epoch in the regression input.

For `Var(loadvar) == load(snapshot, p)`, first reuse a recorded qualified
surface source or a local that holds the exact term. Otherwise consult the
load-variable registration and `registered_load_in_state` for the current,
entry, or relevant explicitly recorded snapshot. Synthesize the other side
at the snapshot it actually names. Reuse the existing equality-across-points
and `old`/`at` machinery where applicable.

Do not print an internal variable as an undeclared source identifier. Do not
use caller `old(...)` to name the callee's entry snapshot: those are generally
different program points. If a required program point is not named, first
determine whether existing recorded selectors or an ordinary retained `mark`
can name it; that must precede the proof that uses it and respect source
attribution. A new snapshot grammar is outside the approved design.

Synthesis may produce a reflexive-looking equality when both operands name
the same registered load. Accept it only when ordinary lowering reproduces
the required canonical equation, including any regenerated guards. Never
replace the obligation with `true` on the strength of the synthesizer's
interpretation. A mismatched snapshot must fail the round-trip check.

### Historical work packages and ownership

These are logical implementation chunks, not a request to run every worker
at once. Use the slots actually available. The coordinator owns shared API
decisions, main execution routing, policy deletion, and the integration branch.
Each worker implements in its own branch/worktree and returns coherent tested
commits, the exact tests run, remaining limitations, and any changed interface
assumption. Do not have agents edit the same checkout concurrently.

#### Package 0 — Coordinator: baseline, feasibility inventory, shared interfaces

- Read this document, root `AGENTS.md`, the proof-object authority boundary,
  and the efficiency/testing docs. Create an integration worktree from the
  current clean primary head and record its exact base.
- Run the normal full gate before experiments. Inventory every `Planning`
  reference and every prerequisite `derive_proposition`/minimal derivation
  route, including `Contextual`, explicit premise paths, conditions, loops,
  and callback/contract-selected calls. Classify each as checked authority,
  smart construction, or obsolete code to remove.
- In a throwaway or task worktree, briefly disable only required-condition
  hidden discharge to identify the current failing obligations. Preserve
  structured reductions/tests, not raw internal dumps. Historical counts
  are a starting point; record additions or cases already repaired upstream.
- Identify exact owning smart sites for the 12 mdtests and two examples.
  Preserve their original C and proof text as acceptance inputs. Distinguish
  the separate two explicit-spelling fixtures and the pre-existing `auto`
  limitation from regressions introduced by this change.
- Agree the payload, identity-query, synthesis, scope-presentation, and local
  candidate interfaces before workers build against them. Shared declarations
  may land as tested additive support, but do not commit a failing fallback-
  disabled prototype or a permanent debug mode.

Deliverable: a reproducible baseline, policy call-site inventory, ownership
assignments, and minimal failing-shape specifications attached to this issue
or the implementation handoff. No new issue files are authorized by this plan.

#### Package A — Exact alpha/load identity and availability index

Owner files: kernel identity helpers and `PureFactContext` representation/
maintenance, their tests, and the smallest call-site exact-query wiring.
Coordinate exports with Package 0; avoid changing surface planner files.

Implement the shared relation and indexed stated-requirement lookup described
above. Support conjunction assembly from stated components, because the two
explicit-spelling fixtures historically relied on hidden conjunction closure.
Keep `Or`, `Implies`, `Exists`, and `ForAll` lookup exact under alpha identity.

Required tests:

- Renamed binder IDs and existential display names compare equal; changed
  free variables, sorts, quantifier kinds, or non-binder subterms do not.
- Nested shadowing and binders inside `And`, `Or`, `Implies`, and `Not` are
  capture-safe; inner and outer variables cannot be confused.
- Registered load versus canonical name matches only for the correct epoch;
  changed-memory cases fail without explicit preservation evidence.
- A stated quantified requirement is available after insertion, unavailable
  after restriction/removal, and independent across persistent siblings.
- Separate conjuncts can establish a conjunction; one disjunction arm alone
  cannot establish its disjunction through this query.
- Deterministic scaling across at least four sizes for unrelated ordinary
  facts, unrelated quantified facts (including same-sort quantifiers), and
  nested binder depth. Count comparator/index work, not just wall time.

Green checkpoint: additive identity/index support and unit regressions. The
production hidden-search removal belongs to the coordinator's cutover.

#### Package B — Faithful synthesis and guard presentation

Owner files: `surface_synthesis.rs` and its tests, narrow presentation adapters
in `proof_object/scope.rs`, `splits_and_scopes.rs`, and introduction handling.
This worker owns any necessary lowering presentation record; coordinate any
kernel-file edit with A rather than editing the same file independently.

Implement binder naming/rebinding, guard-child presentation preservation,
folded named-range spelling, and load-defining equation synthesis. Use A's
identity interface for round-trip tests once available. Do not implement the
global requirement retry loop or expand the atomic checkers.

Required tests:

- Both examples' actual load-equation shapes synthesize, parse, and lower to
  the same requirement at the correct program point; wrong snapshot and
  unresolvable-variable variants are rejected.
- Existing static-object/range synthesis tests remain green, including
  nonzero starts and folded byte-to-element counts for more than one element
  size. Never infer a range start from an unrelated index.
- A renamed universal following a hidden guard uses the spelling in its
  written body; an existential witness remains well-scoped.
- Nested `both` over hidden guards retains the right written body, renders,
  and re-verifies. Removing a required guard proof fails.
- Unsupported correspondence is a bounded synthesis/construction failure,
  not an unrenderable accepted smart proof.

Feasibility exit: real example load equations round-trip and representative
guarded nested proofs expand without any new grammar or proof operation.
If this cannot be demonstrated, stop cutover and report the exact mismatch.

#### Package C — Local composition of witness, transport, and coverage

Owner files: a focused requirement-closure planning module or a narrowly
bounded section of `smart_closures.rs`, transport helpers in
`smart_execution.rs`, and composition regressions. Prefer a separate module
if that avoids overlapping coordinator edits to execution entry points.

Build the local candidate input and checked composition described above.
Start with an explicitly opened requirement `have` in a test, so this package
does not depend on the coordinator's automatic retry loop. Use B's fixes as
they become available; kernel identity/index additions come from A.

Required tests:

- Concrete and caller-existential witnesses produce complete checked bodies.
- The actual local-declaration snapshot boundary from a dynamic `cstr`
  fixture is preserved and handled by explicit transport/coverage.
- Zero-length/empty-domain and definedness boundary cases do not turn an
  invalid witness into a vacuous proof.
- A genuinely invalidated permission rejects transport; a necessary premise
  or transport deleted from an explicit certificate causes rejection.
- Unrelated facts and irrelevant existential requirements do not enlarge
  candidate selection; candidates of the wrong sort are ignored.
- A candidate miss or budget exhaustion leaves the parent proof unchanged
  and returns a bounded diagnostic.

Feasibility exit: the dynamic requirement closes and its explicit Surface
proof verifies through the ordinary entry point with the original C intact.
Do not broaden general-purpose smart heuristics merely to make this one
composition happen accidentally.

#### Package D — Coordinator: structured reporting and retained-`have` orchestration

Owner files: `ClickError`, transition certification, statement checked drivers,
main smart execution routing, and the requirement-planner module wiring.
This is the serial integration chunk because it touches shared control flow.

Implement payload propagation and the smart-only retry operation. Attach
presentation through B's adapter, match with A's relation, and close using C
plus existing simple/smart closure support. Preserve `Have` ancestry and source
origin. Test a real checked descendant, not merely rendered evidence text.

Audit `try_statement_step` and every caller before changing its behavior:
explicit proof checking must retain the bare checked operation, while smart
`execute`, `execute_until`, implicit/`auto` execution, preservation planning,
and branch-path planners must all use the appropriate smart wrapper. Preserve
`step_contract`'s selected contract/resource arguments if its call requirement
uses the same dispatcher. Never drop the selected contract during a retry.

Error swallowing is a specific risk: candidate helpers that turn an error
into `None` must give the requirement planner a chance to consume the payload
at the correct frontier, and ordinary non-requirement failures must keep their
normal diagnostic behavior.

For branch-local calls, insert the `have` inside the arm after its assumptions
are available. For requirements created during expression/condition evaluation,
preserve the kernel's guard and provenance. Do not hoist an unguarded fact
above the branch or use scratch successor facts to prove it. If the supported
consumer needs different placement, implement it through its existing checked
branch/execution operations and retain that proof structure.

Required tests:

- The disjunction call expands with its required `have`, verifies cold, and
  fails when that specific `have` is removed; bare explicit `step` fails.
- Explicitly stated requirements succeed without smart requirement search.
- Two sequential calls retain their separate facts at the correct frontiers;
  a multi-requirement call makes progress without repeating a `have`.
- A failed `have`, repeated alpha-renamed obligation, or non-requirement error
  publishes no successor or leaked fact and does not reset the smart budget.
- Branch-local insertion, selected-contract calls, and at least one scoped
  execution/loop consumer preserve placement and ordinary expansion.
- The generated proof belongs to the selected smart site; unrelated proof
  containers and neighboring smart sites are unchanged by expansion.

Green staging: additive helpers and direct helper tests may land before the
switch. Keep the old production dispatch until all required paths are ready;
the final switch must not introduce a user-visible dual mode or new flag.

#### Package E — Coordinator: cutover, policy removal, complete verification

Dependencies: A, B, C, and D feasibility exits are satisfied on one coherent
integration base. This package cannot safely be delegated to an agent working
against stale independently chosen interfaces.

- Switch all required call-precondition consumers to exact availability or
  structured reporting, and all smart callers to retained proof construction.
- Remove `StatementPrerequisitePolicy::Planning` and obsolete hidden
  prerequisite derivation paths. Revisit the Package 0 inventory and account
  for each removed branch's other duties, including condition filtering and
  automatic transport. Do not remove legitimate checked evidence solely
  because it shares a struct with the old fallback.
- Ensure no required condition falls back to `Contextual` logical derivation
  or an explicit-context minimizer during simple checking. Any remaining atomic
  evidence must obey the frozen-rule and explicitly selected-premise contract.
- Remove temporary debugging, duplicate engines, and test-only bypasses.
  Preserve the zero body-rerun baseline.
- Update the smart/simple tactic and proof-object documentation if their
  descriptions need clarification. Delete this issue and its existing README
  entry only after implementation, regression coverage, and documentation are
  complete; a design-only change must retain the issue.

### Historical dependency order and practical dispatch

Recommended order for a coordinator with three worker slots:

1. Coordinator completes Package 0, freezes shared interfaces, and assigns
   nonoverlapping ownership. Baseline and failure-shape discovery are serial.
2. Dispatch A, B, and C. C can first write/test its composition against an
   explicitly stated requirement; it need not wait for automatic reporting.
   B can work on syntax/provenance while A builds the identity index.
3. Coordinator implements the error carrier and other independent parts of D,
   without concurrently editing B/C-owned methods. Workers return tested
   additive commits and precise integration notes.
4. Integrate A, then B and C in their dependency order. Rebase workers when an
   interface changes; do not resolve semantic disagreements with textual
   conflict resolution alone. Complete D on the combined base.
5. Run the early feasibility exits, then perform E and the full acceptance
   matrix. An available worker may independently review authority, snapshot
   correctness, or scaling on the frozen integration commit while the
   coordinator runs the gates.

With fewer slots, run the same packages in order; parallelism is an execution
choice, not part of the design. Do not split the retry state machine, the
meaning of equality, or final policy removal among several agents. Those need
one owner each. Do not ask each worker to "make all fixtures pass"; that
invites overlapping heuristic fixes and incompatible assumptions.

Each worker's handoff should include:

- Base and commit IDs, owned files, implemented interface contract.
- Tests run and their exit status; whether a full gate was run on that commit.
- One successful explicit proof/round-trip for the capability it adds.
- Negative cases and scaling dimensions covered.
- Any unresolved assumption, missing source spelling, or proposed scope change.

Green checkpoints may retain the existing fallback while adding tested
support. A fallback-disabled red prototype stays uncommitted in its isolated
worktree until repaired or replaced with a green checkpoint. Only coherent
green commits enter the primary checkout. Before primary integration, verify
the primary is clean and still at the recorded base; if it moved, update the
integration branch and rerun affected gates. Integrate with Git, never by
copying partially edited files.

### Historical acceptance matrix and verification procedure

Use the actual source locations selected by parsing/current tooling; do not
hardcode stale line numbers from this design. Production workflows and tests
call the shared bounded verification/expansion APIs directly. The existing
`verify_c0_sources`, `expand_c0_tactic_source_at`, and claim-expansion tests in
`statement_steps.rs` show the in-process regression pattern. Do not create
recursive Click subprocess wrappers or parse stderr to recover obligations.

| Dimension | Required evidence |
| --- | --- |
| Basic audit boundary | Disjunction example verifies automatically; expansion retains the necessary `have`; ordinary cold verification succeeds; deleting that `have` rejects the call |
| Explicit simple checking | A bare missing-precondition `step` fails without planner invocation; a matching explicit `have` succeeds; unrelated simple statements retain behavior |
| Historical affected corpus | All 12 named mdtests, both named examples, and both explicit-spelling fixtures verify with original C and proof text; any newly discovered affected case is also covered |
| Generated proof coverage | Relevant smart sites in each affected family expand and re-verify; generated `have` bodies contain explicit checked proof operations; already-exact obligations need no gratuitous `have` |
| Binder identity | Capture, shadowing, connective nesting, sort distinctions, binder-name changes, and changed non-binder terms are tested |
| Guard fidelity | Hidden guards before written implications/universals, existential conjunct guards, and nested `both` all remain provable/renderable only with their full obligations |
| Snapshot correctness | Load-equation round trips name the right epoch; dynamic string proofs include checked transport; invalidating effects and wrong snapshots reject |
| Locality | Four-or-more-size deterministic tests independently vary unrelated ordinary facts, unrelated quantified facts, binders, and multi-requirement calls |
| Persistent authority | Failure/branch siblings retain their original state; nested proof joins cannot publish another scope's goal, witness, resources, or execution frontier |
| Routing coverage | Linear `execute`, `execute_until`, automatic execution, branch/scoped execution, and selected-contract call paths cannot fall back to hidden call search |
| Tools | Ordinary verification first; then relevant expansion/audit sites, cold rechecking, and fixed-point checks through the ordinary tool boundary |
| Final gate | Unfiltered `scripts/check.sh` exits zero and both fixture harnesses retain zero body reruns; no budget increase or quarantine expansion |

For focused fixture work, the existing `MDTEST_FILTER` and `CLICK_EXAMPLE`
environment selectors may be used with the contained nextest harnesses. Those
filtered runs skip the full body-rerun census and do not replace the final
unfiltered gate. Judge the gate from its unpiped exit status. Preserve the
repository's normal budget and process-containment settings.

Do not assert that removing every generated `have` always fails: a fact may
be redundant in a larger proof. Pin necessity in deliberately minimal
regressions, and separately check complete expansion of the real corpus.
Likewise, do not require byte-identical hidden states between an automated and
expanded run; require the same claim to verify and the certificate to expose
its actual operations.

If a run times out or is interrupted, confirm the verifier process tree exited
before interpreting subsequent timings. Unexpected slowness, uncheckable
certificates, expansion disagreement, or oversized raw diagnostics are tooling
failures to reduce and fix before proceeding. A prompt bounded candidate miss
is a planning limitation: use the explicit composition to identify the missing
selection, not a larger timeout.

### When to revise this design

The coordinator may choose exact private type names, module boundaries, or
equivalent indexed representations without further approval. Record changes
to shared interfaces before dependent workers continue.

Escalate the design question with a concrete reduced requirement if:

- The original load equation has no faithful expression even with existing
  recorded selectors and ordinary proof marks.
- The dynamic string composition lacks a checked simple transport/coverage
  operation rather than merely lacking a planner to select it.
- Correct presentation would require changing the proposition's meaning,
  adding a trusted rule, or accepting a certificate that cannot be expressed
  in ordinary Surface Click.
- A proposed identity/index solution requires scanning unrelated context or
  loses the distinction between memory epochs or free/bound variables.

In those cases, report what has been established and the smallest remaining
gap; retain a green checkpoint. Do not claim this issue solved by weakening its
acceptance corpus, changing verified C, retaining hidden search elsewhere, or
deferring the missing proof inside an unverified example.
