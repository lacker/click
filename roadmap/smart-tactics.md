# Smart tactics: fast checking and enforceable search boundaries

Priority: P1.

Soundness: not soundness. This is a checking-cost and search-boundary audit.
Removing automatic reasoning must preserve ownership, aliasing, initialization,
width, lifetime and provenance refusals; inability to prove separation is not
permission to write or preserve a value.

## Goal and audit boundary

A simple checking operation costs its explicit input and necessary state delta,
up to indexing factors. With those fixed, more ambient facts, owners, aliases,
loans, cached observations or execution history must not make it slower.
Expensive discovery belongs in budgeted, expandable search, whose expanded
steps satisfy the same checking rule. A fast special case does not establish
this guarantee for an operation's other routes.

The operation inventory starts from the `c53645952` baseline (2026-11-11,
PR #2520); the frozen dependency counts below reflect the current interface split.
It organizes the next measurements; it is not a claim that all checking paths
have been audited, or that every candidate below is a reproduced defect.
The interface refactor now exposes discovery through `kernel::search::ProofSearch`
without changing its behavior. The frozen
[dependency inventory](../build_support/proof_search_edges.tsv) records existing
callers and separates operation dependencies from the explicit `ProofDriver`
and mixed callers classified in the [caller audit](../design/proof-boundary-classification.md). The driver owns proof interpretation and the
choice between explicit obligation proofs and implicit solving. The
operation-to-driver migration list is now empty;
implicit solving by the driver is legitimate expandable work. No new scaling measurements accompany that split.
Existing test names below identify evidence to retain and inspect, not new
measurements. The contract lives in [Verifier design](../docs/internals/verifier-design.md)
and [Verification efficiency](../docs/internals/verification-efficiency.md).

The scope includes checking called by `step()`, explicit tactics, certificates,
entry setup, joins and completion. The implicit closer is separate from step
checking even when a bare step invokes it. Arithmetic premise discovery in
`solve` or that closer is legitimate search if budgeted and expandable;
applying its explicit certificate is checking. Trace printing, independent
expansion audits and debug-only cross-checks are distinguished from ordinary
checking, not counted as production scans merely because they iterate.

An index is not by itself a complexity argument. Enumerating a large bucket,
equality class or chain can still be ambient search. Nor may an implementation
justify eager derived facts or cache rebuilding by calling them output: the
delta must be required by the selected rule. Amortized claims need a total-work
argument across repeated steps and persistent forks, as well as cold misses.

## Reading the inventory

- **Scoped evidence:** named tests cover particular routes and growth axes;
  this does not certify the whole operation.
- **Source candidate:** a growing traversal exists on an identified path;
  a complete-operation red curve is still required before choosing a fix.
- **Reachability gap:** a helper scans, but its supported source caller or
  producer has not been established.
- **Coverage gap:** a path or growth axis has not been established by this pass.
- **Deferred evidence:** another roadmap owns a previously identified problem;
  its old counts are not fresh measurements. Existing priority stays unchanged.

There is no defensible total bug count yet. Rows are operations, not bugs;
several rows share helpers and a row can contain multiple routes. The previous
six-group estimate covered only resource/loan candidates, not the verifier.

## Reconciled status and ownership

The frozen inventory has **642 reference records**: 4 legacy bridges, 17 callers
of those bridges, 6 operation references, 0 operation-to-driver references,
16 mixed references, 122 driver references, 469 search references, 6 presentation
references and 2 imports. These are neither independent walks nor
runtime invocation counts. The [caller audit](../design/proof-boundary-classification.md)
classifies every mixed and operation-to-driver record and groups all 6
operation references. Registering the signed-definedness and unsigned-order
helpers exposes four existing search-only caller records; it adds no runtime work.

- **Confirmed architectural exceptions:** explicit legacy transport invokes
  discovery.
  Its fixed-state route retains uncharged transition-assumption reconstruction. No fresh
  scaling curve was run for this reconciliation.
- **Unmeasured candidates:** four kernel bridges map to three groups, L1, R2
  and C1. Other transition and declaration checks
  need caller-specific evidence. Preserve these as candidates, not confirmed
  performance regressions.
- **Legitimate search:** driver-owned implicit solve and explicit smart
  planning. Generating obligations is fast work; solving them may be slow and
  expandable. Have/claim and resource-scope obligation scheduling, step/fold dispatch,
  and retained step/fold completion are no longer open extractions.
- **Transport coverage:** the remaining inventory below covers written syntax and
  retirement. Scalar
  conjunction selection/regrouping and matching compound/nested implications
  with scalar leaves have ordinary expansion coverage. They do not settle
  non-scalar leaves, binders, other proof contexts or legacy retirement.
- **Separate owners:** the representation split in
  [unspellable facts](unspellable-facts.md) owns the remaining shared-term
  migration boundaries. Its original R1–R7 reproductions are closed; use its
  current closure checklist for remaining work. Those identifiers are local to
  that document, not this ledger's R1/R2. M1, E1 and Q1 retain the adjacent owners below.
- **Operation guards:** theorem application, scope completion, statement-result
  publication, prepared-step publication, have opening and contract-claim opening
  have test-build discovery guards.
  Statement preparation retains loan-access, raw ownership-validation and
  composite-framing dependencies. First guard failures mask later crossings;
  re-probe complete preparation as each route is removed. See the [reproductions](../design/proof-boundary-classification.md#operation-discovery-guards-and-reproduced-crossings).
  Statement preparation remains unguarded; no exception exempts its search.
- **Enforcement gap:** lexical dependency freezing and selected work counters
  do not prohibit every search call during expanded replay or detect arbitrary
  loops, shared-term export and copying. No global fast-proof guarantee yet.

Resource-scope completion now reports obligations to the driver, including
nested opens; function-exit deferral is unchanged. C-branch and proof-case script
interpretation now also lives in the driver; primitive split/focus/join operations
do not run arm-script callbacks. No operation-to-driver records remain in the frozen inventory.
For a new scaling experiment, L1 through an actual write remains a bounded
candidate. Boundary cleanup and enforcement are alternative next slices below.
Transport work should target a surviving generated form or a written legacy
consumer and its retirement criterion, not accumulate already-covered shapes. These are separate
work items; this reconciliation changes no behavior.

### Remaining obligation generation

Step preparation retains emitted verification conditions and call preconditions,
and fold preparation retains its body facts, even when already known. The driver
proves each obligation with a written block or ordinary `solve`. This does not
finish evaluator migration. Executed uint32 division and remainder now always
retain their ordinary nonzero-divisor obligation; generation has no ambient
fact-context parameter and expansion writes a step proof that replays without
implicit solve. Other arithmetic operators still decide some safety conditions
before emitting any obligation. Replacing those decisions needs
round-trippable goals and flat generation/publication costs. The earlier, unlanded arithmetic-migration prototype failed `struct_array_element_expands_with_its_subscript`
(the initialized-global sum has no round-tripping overflow-goal spelling) and
`straight_line_assignments_cost_the_same_at_every_position` (work grows from
2765 to 2885 across twelve assignments). These are prototype findings, not
current failing tests; reproduce them when revisiting that migration. Retain
those controls for that slice.
The step/fold preparation migration is complete for the covered named,
population/authority, operational-wrapper and legacy-outcome routes. Keep its
no-reexecution, input-obligation and retained-endpoint invariants in
[the architecture](../docs/internals/architecture.md) and the scoped preparation
controls in `src/scaling_tests/surface/tests/tactic_tests/statement_steps.rs`.
Do not reopen those tasks under the broader lifecycle row E1.

Have/claim opening still uses the driver's `with_proved_lowering_requirements`
probe/reinvoke adapter. Solving belongs to the driver there; any repeated-lowering
cost needs its own fixed-input/ambient-growth measurement. This is not evidence
that the removed step/fold retry survives.


## Operation map

Paths in this table are relative to `src/`. Detailed outstanding measurements
follow it. None of these whole-operation rows is marked complete.

| Operation and intended cost | Checking entry points | Existing scoped evidence | Remaining evidence or candidate |
| --- | --- | --- | --- |
| Prepare selected code and function entry; pay once for selected declarations and clauses | `surface/verification.rs`, `kernel/functions.rs`, `kernel/termination.rs` | `surface/tests/step_shape_scaling_tests.rs`: `entry_setup_is_linear_in_owned_parameters`; `kernel/termination/termination_scaling_tests.rs`: call-chain, fan-out and cycle controls | Coverage gap: complete frontend/lowering/termination dependency map; no per-step rebuilding of prepared input. These are setup costs, not constant-size steps. |
| Execute a scalar statement or access; pay for selected expression and affected storage | `kernel/eval.rs`, `kernel/proof/execution.rs`, `kernel/primitives/memory_state.rs` | `kernel/tests/memory_scaling_tests.rs`: `one_store_is_logarithmic_in_unrelated_cells`, `sequential_owned_parameter_stores_ignore_earlier_cached_fields`; source step-shape tests | Memory/cache candidates M1; ownership and loan checks below are dependencies of the whole step. A flat store helper alone is insufficient. |
| Admit facts and decide a condition; pay for named terms and justified incremental updates | `kernel/assumptions.rs`, `kernel/equality_graph.rs`, `kernel/difference_graph.rs`, `kernel/assumptions/condition_reasoning/decision.rs` | `kernel/assumptions/condition_buckets.rs`: `equality_class_hits_and_anchored_misses_stay_indexed`, `interval_queries_do_not_walk_symbolic_order_components`; graph late-merge/fork controls | Pointer distinctness uses explicit separation; ownership discovery is removed. Coverage gap: total admission/propagation work across growing shared classes, beyond covered shapes. |
| Select, consume, fold or unfold ownership; pay for explicitly selected pieces/body | `ResourceContext::{satisfies_fact,without_fact_incrementally_impl,consume_unit_owned_memory}`, `ExecutionProofCore` fold construction | `kernel/loans/tests.rs`: `call_fragment_composition_stops_at_a_fixed_gap`; `kernel/proof/execution/tests.rs`: `constructing_an_instance_fold_pays_for_its_body_once`; source fold/unfold controls | R1 reachability gap for other quantities; R2 source candidates for ownership validity, alias/root discovery and overlap. |
| Observe separation or resource facts; pay for selected operands/evidence | `surface/proof/proof_object/splits_and_scopes.rs`, `kernel/proof/facts.rs`, `kernel/assumptions/memory_reasoning.rs` | source `observing_one_owner_ignores_unused_parameters`; transport footprint tests, including `two_footprints_do_not_expand_into_a_cartesian_product` | F2: composition/member bucket growth remains a coverage gap; frontier opening no longer reconstructs a composition-only context. |
| Check a write against loans; pay for selected conflict/evidence, not all loans or aliases | `LoanLedger::permits_memory_access_with_assumptions`, called by memory-access checking | `kernel/loans/tests.rs`: `write_barrier_does_not_enumerate_overlapping_loans`, `writes_without_active_memory_loans_do_not_walk_pointer_aliases` | L1: aliases with active loans and symbolic-loan comparisons. Zero-loan and concrete-overlap controls do not finish this operation. |
| Apply a modular call, transfer resources and finish it; pay for selected contract and effects | `kernel/functions.rs`: `execute_verified_function_applications_with_suspension`, `call_kept_ownership`; `kernel/proof/execution.rs` | source `a_call_ignores_unrelated_owned_objects`; `kernel/functions/stable_view_call_tests.rs`: `returning_one_borrowed_owner_does_not_rebuild_its_memory_block` | C1: resource-family selection and selected-address composite candidates; non-direct member-count preparation is now flat. E1: execution/publication/completion accounting. |
| Split/join branches and enter/exit loops; pay for explicit arms/interfaces and actual changes | `kernel/api.rs`: `abstract_c_state_for_interface_join_across`; `kernel/loops.rs`; `kernel/proof/execution.rs` | `kernel/loops/contract_exit_join_tests.rs`, `kernel/loops/frame_resource_tests.rs`; branch availability and interface-join controls | J1 coverage gap: fixed-delta joins across growing stable state; loop-head abstraction uses a different policy. Existing growth allowances do not establish ambient independence. |
| Apply an explicit equality, arithmetic certificate or preservation step; pay for written nodes/premises | `kernel/proof/{preservation,integer_arithmetic,term_rewrite}.rs` | `kernel/proof/preservation.rs`: history independence, explicit-step linearity, selected resource fields; `kernel/proof/integer_arithmetic/tests.rs`: repeated premise and shared-DAG controls | Coverage gap: map every Surface certificate driver through lowering, premise lookup, application and publication; preserve cold expansion/replay evidence. Do not re-enter discovery during application. |
| Introduce binders, apply logical rules and publish checked results; pay for explicit proof structure | `ProofObject::apply_intro`, `ProofFacts::freshen_integer_forall_body`, proof execution event recording | selected term-rewrite, fact-key and event-publication controls | Q1 deferred nested-quantifier work; E1 deferred/revalidation candidates. A helper's flat lookup says nothing about repeated whole-body copying. |

Test paths in the evidence column are relative to `src/scaling_tests/`.
The source-level control suite is
[`step_shape_scaling_tests.rs`](../src/scaling_tests/surface/tests/step_shape_scaling_tests.rs).
It holds repeated roles to a no-drift rule and varies ambient objects/facts;
it is valuable integration coverage, not an exhaustive list of statements,
contracts, or resource shapes.

## Remaining transport expansion inventory

The remaining work is written-proof migration, removal of residual internal
legacy producers, and syntax/dispatcher retirement. A selected expansion of
`integer_sum_range_fold.md` and `rewrite_pointer_into_a_shifted_byte_view.md`
still retained legacy nodes during the corpus pass; migrate these producers
alongside their written consumers before deleting the dispatcher. Counts are syntax sites, not independent slow walks or a claim that
every fixture currently verifies.

### Written syntax is a separate migration

A balanced-parenthesis scan of `.click` files and Click fences in Markdown,
excluding prose and Rust test strings, leaves:

| Corpus | Files | Sites |
| --- | ---: | ---: |
| `mdtests/` | 72 | 125 |
| `examples/` | 29 | 369 |
| `library/` | 0 | 0 |
| Total | 101 | 494 |

The 18 mdtests with failure expectations still require migration while retaining
their semantic refusals. Sixteen positive fixtures also supply exact input text
to expansion/mutation tests; migrate those inputs together with their tests,
rather than replacing a smart test input with an already-expanded proof. Positive fixtures also need full-file verification:
selected-tactic expansion verifies a prefix, so it does not establish that the
rewritten proof's remaining suffix closes. Remaining groups include historical
initializedness, computed range bounds, loop frames, and call preservation.
The final corpus pass and syntax/dispatcher deletion remain distinct tasks.

### Migration blockers to resolve

- Migrate the negative `transport_wide_viewable_range_to_element_definedness.md`
  fixture without inferring initialized contents from its pure `viewable`
  premise. Its legacy rule must remain refused; initializedness needs an
  initialized input clause, a write, or an explicit definedness premise.
- The unchanged `rbtree/rbtree-insert` example fails while re-folding its initial
  node, before its legacy transport calls. An explicit `node == identity`
  lookup moves the failure to the packed parent-pointer equality. Repair and
  verify this baseline before migrating its 106 written sites.

### Excluded or still unconfirmed

Do not count these as additional confirmed generated-output families:

- `named_root_call_preserves_aliased_pointer_field` reaches its unchanged
  deterministic smart-work limit while proving `cursor->left == rid` after the
  helper call. Repair that proof explicitly before migrating its written sites;
  a successful expansion prefix is not a passing whole-fixture regression.

- Computed lower endpoint `p[index + 1..length]`, nested upper endpoint
  `p[index..index + 1 + 1]`, and native upper endpoint
  `p[index..index + 1u64]`: the reduced probes fail with both plain and
  restricted solve. The narrow probes supply `0 <= index` and the appropriate
  upper bound (`index < length` or `index + 2 <= length`); the wide probe
  supplies `index < length`; all supply `viewable(p[0..length])`. These are
  search misses, not successful expansions retaining transport. This does
  not establish that every spelling of these shapes fails.
- Bare same-state range `transport` in a C proof, in both narrow and native
  form, misses its source-only premise search in the tested examples. Bare
  `transport` is not available in pure theorem proofs. Neither result is
  evidence of another generated-output family.
- `bound_universal_outcome_retains_instantiation_and_transport` fails in
  `bubble_pass3` before expansion, while proving the loop's quantified bound.
  It is not a current positive regression for its old output assertion.
- `quantified_old_transport_expands_to_one_quantified_frame` and
  `quantified_old_transport_substitutes_its_introduced_binder_on_the_checked_proof`
  both fail before expansion at the shifted-copy store's separation
  prerequisite. Whole-quantifier transport is still unconfirmed by a passing fixture.
- Residual scalar/address variants, logical wrappers beyond these examples,
  and other proof-context adapters remain source-audit candidates. They get
  another work item only after a successful expansion demonstrates it.

### Producer paths and retirement boundary

The principal remaining producer anchors are
`surface/proof/surface_certificates.rs::plan_explicit_universal_conclusion_discharge`
and `plan_explicit_loadability_transport`,
`surface/proof/smart_closures/search.rs::try_carry_entry_conjunct`,
`surface/proof/smart_execution/search.rs::{try_execution_fact_transport,fact_transport_candidate_search}`,
and `surface/proof/proof_object/execution_statements/search.rs`'s planned
transport adapters. These construct `TransportUsing`, but the driver can replace
that construction with ordinary steps. A constructor occurrence alone is not
an additional surviving expansion.

The legacy fixed-state route still rebuilds transition assumptions with
`assume_proposition_uncharged`; its source acknowledges path-linear work.
The endpoint is to make that implementation unreachable from expanded proofs,
then remove it, including obsolete source/result normalization and
premise/effect collection. Finish with a boundary test that an expanded proof
cannot create `ProofSearch`; a text search alone is insufficient.

The next sequence is migration of the remaining written corpus, then syntax
and dispatcher retirement. Preserve negative fixtures' semantic refusals during
migration. Missing primitives or newly reproduced output shapes require a new
design discussion rather than silently expanding a chunk. This inventory does
not claim exhaustive coverage of all possible source programs or the unrelated
fast-operation ledger.

## Outstanding measurement ledger

### R1: remaining fragment-selection routes — reachability gap

In [`resource_algebra.rs`](../src/kernel/primitives/resource_algebra.rs),
`without_fact_incrementally_impl` enumerates/normalizes suppliers outside the
view and unit-owned routes; `satisfies_fact` has the corresponding other-quantity
route. Surface validation rejects quantities directly on memory. First identify
a supported producer and complete fold/transfer caller, or establish that the
route is unreachable and remove/classify it. If reachable, fix one requested
footprint and grow rejected suppliers; separately grow genuinely consumed
pieces. Test symbolic/wide carriers, gaps, ambiguity and persistent parents.

### R2: ownership validity and overlap — source candidates

Entry-state call borrows rejoin their selected residual frame without memory
alias discovery. A private transfer restores the identities retained at call
entry. Newly produced ownership, post-state outputs, raw body-return descriptions
and contract comparisons retain their validating path. The restoration guard and
`call_borrow_restoration_ignores_ambient_aliases_and_frame` cover this selected
join, with unrelated aliases, unrelated owners, and repeated forks; they do not
certify all call preparation or output-description lowering.

Call preparation no longer rebuilds an optional population partition with
`retained_population_call_partition`. The five affected `memset` proofs use
explicit separation and single-footprint preservation for both values and
read definedness. `preserve` requires the exact old definedness fact; it does
not reconstruct history or infer initialization from ownership. The guarded
proof expands and replays without implicit solve or legacy transport.
This removes optional composition inference, not ownership validation.

A source partial-borrow probe still grows with unrelated aliases after the
removal; deleting this inference cuts a fixed amount of work in that probe,
not its remaining growth. Keep the complete-call cost separate from the scoped
composition-retention guard.

`owned_validity_candidates` and incremental validity checking still have
symbolic-bound and multiple-coordinate-origin paths. Single-block count and
constant-coordinate neighbor shortcuts do not settle multi-block alias/root
discovery. Selected overlap checking now uses the supplied ranges and indexed
base/endpoint equality, without enumerating aliases. Its fixed-query alias
regression and translated-address refusal controls do not settle the separate
candidate-selection scan or the cost of a complete ownership insertion.

Instance `unfold` now replaces the exact held parent with its selected body
through `ResourceContext::unfold_instance_body`, using the framed definitional
exchange `R * F -> body(R) * F`. It does not search the frame for memory overlap
or generate a new separation obligation. Exact exclusive-resource checks remain;
definition, arm, parent ownership and child-identity checks remain in the rewrite.
The replacement has a test-build discovery guard.

Unfold publishes its justified consequences without querying the caller's
stated-fact index. Exact duplicates within the output batch are removed locally;
normal fact admission handles facts the caller already holds. This avoids
forcing deferred keys for unrelated facts merely to suppress an output.
Fold body-clause publication and returned-instance body-fact publication follow
the same rule. `resource_publication_ignores_unrelated_stated_facts` checks a
fixed matched body whose pure clause is already held, with 4/16/64 unrelated
pointer equalities. It measures each producer and admission of its output twice.

Written folds already prepare a conditional successor with
`retaining_required_obligations`, return body clauses to the driver, and require
explicit proofs or implicit `solve` before completion. The regression
`prepared_fold_emits_body_obligation_without_indexing_ambient_facts` exercises
that preparation mode with a cold index and checks the returned obligation:
33 / 33 / 33 units, including the test's obligation construction.

The ignored `legacy_checked_fold_requirements_ignore_unrelated_stated_facts`
diagnostic calls the lower-level rewrite without obligation retention. Its
83 / 155 / 443 units (including obligation construction) do **not** describe ordinary written-fold preparation.
Identify a production caller using that checked mode before treating it as a
remaining fast-path violation; do not add a second obligation mechanism.

`instance_unfold_ignores_ambient_pointer_aliases` measures complete kernel unfold,
the selected replacement, and publication/reinsertion of its facts at 4/16/64
aliases with one body cell and one retained owner. The caller's stated index is
left cold. Both adjacent ownership and contradictory memory premises retain
persistent parents. Complete kernel unfold costs 370 / 370 / 370 work units;
publication and reinsertion together are also flat (248 units for the adjacent
case, 190 for the contradictory case). These are bounds for this fixed body,
not all unfolding routes or Surface materialization.

The ignored `raw_ownership_admission_must_not_search_ambient_pointer_aliases`
diagnostic retains the separate raw-admission growth and overlap-refusal control.
Raw ownership admission and output-description validation remain callers to
diagnose and migrate.

Hold one inserted owner and one relevant neighbor fixed. Independently grow
same-block owners, owned blocks, coordinate origins and exact/offset aliases;
use symbolic bounds and different origins, not just the indexed constant case.
Measure the complete ownership addition/fold, including successful disjointness
and overlap refusal. Distinguish this from output-sized explicit composition.

### F2: separation observation — remaining coverage

Frontier `have` opening no longer constructs a composition-only context or
admits the selected separation from it. Its explicit proof must establish that
fact. `have_opening_does_not_copy_ambient_compositions` grows unrelated owners
at 4/16/64 with a fixed selected goal and proof.

Other selected observation routes still need composition/member bucket growth
coverage. Pointer decisions consume explicitly stated separation instead of
discovering it through ownership compositions or alias classes. Removing this
copy does not establish a bound for every separation observation.

### L1: write restrictions from active loans — in-progress migration

The pointee-store route generates a separation obligation without alias
search. The source write regression is flat at 179 charged units with one loan
and 4/16/64 aliases (110 without a loan); these measurements cover this route,
not the remaining callers below. Explicit source proofs retain typed subobject
extent and designation. The `contains_element` law supports signed 32-bit and
unsigned 64-bit interval bounds without wrapping the selected upper endpoint.
Exact pointer argument spellings use an entry-built index; enclosing recorded
requirement clauses use the existing conjunct index. Keep the position-drift,
expanded-replay and negative ownership controls alongside the loan measurements.

Pointee scalar stores return an ordinary separation obligation against a retained
resource descriptor of active loan backing. Loan opens/closes update a persistent
fixed-width identity trie; generating the obligation clones its root. The driver
runs ordinary `solve`, whose conjunction case emits the existing `separate_star`
and `separate_symm` applications. Restricting a larger separation emits
containment proofs and `separation::separate_restrict`; candidate selection belongs only
to `ProofSearch`. The store adds no e-graph facts; the separate
`contains_element` library axiom supplies explicit interval-to-cell containment.
`one_write_with_a_loan_does_not_walk_unrelated_aliases` measures the complete
source write with one view and 4/16/64 aliases; `loan_access_requirement_is_retained_and_branch_local`
covers descriptor generation and persistent closes with 4/16/64/256 loans.
These scoped controls do not certify every loan caller or proof-publication cost.

Local assignments, bulk writes, free, loop checks, and resource rewrites still
use `permits_memory_access_with_assumptions`. Its empty-loan decision now stays
outside `ProofSearch`; active-loan callers retain alias enumeration and symbolic
range comparisons. Migrate each actual caller to explicit obligations or isolate
its bounded structural rule. The local-assignment prototype also exposed
obligations for compiler-generated storage; resolve their pre-state spelling
before migrating that route. Do not restore a search fallback for missing proofs.

Independently grow symbolic loans at fixed aliases, cold/repeated queries, and
persistent branches. Cache retention is separate from write permission: its
selected-separation check now tests endpoints directly instead of using the
alias-searching membership evidence builder. Retain nested-loan, width,
overlap and ended-scope safety controls.

### C1: modular call framing — source candidate, also in scaling roadmap

When a verified call has memory effects,
[`functions.rs`](../src/kernel/functions.rs) calls `call_kept_ownership` on the
caller frame. Field-bearing instances stay opaque: call preparation does not
open their bodies or gather their memory/facts. With no owned composites, the
frame is retained directly without constructing `ProofSearch`. The selected
instance-count regression guards that route against discovery.

The retained-instance route is covered by a discovery guard and the fixed-call
instance-count scaling regression. The arena proof uses explicit separation
and preservation for its selected retained headers and cells. Automatic
statement-exit fact restatement is removed; calls publish producer facts at
their original states rather than searching for extra current-state facts.

Experimental removal: `ProofSearch::call_frame` no longer opens retained
non-argument-direct composite bodies to discover hidden memory ranges. It
retains ownership unchanged and adds no replacement obligations or bonus facts.
The argument-direct family selection and lazy selected-address opening remain;
neither family-count independence nor bounded candidate lookup is established.

`call_frame_preparation_must_not_open_unrelated_composites` grows one retained
family at 4/16/64 members, with a fixed one-cell call effect. It covers a nested
one-cell wrapper and a load-dependent range body. Preparation work is now
1 / 1 / 1 in both cases (previously 1,078 / 4,294 / 17,158 and
1,926 / 7,686 / 30,726 respectively). The regression checks that no opened
ranges are recorded. Setup, havoc and observation are outside the meter, so
this is scoped frame-preparation evidence, not a complete call/step bound.

The normal examples and markdown proof corpus both pass without proof repairs
(104s and 353s). No C, contracts, axioms, obligations or e-graph reasoning changed.
The population-membership safety test now expects opaque composite wrappers to
record no hidden private range, retaining its shared-mutation rejection checks.
Validation: 1,866 normal scaling/affected-module tests pass, plus the one
directly affected nightly publication-scaling test. The full nightly was not run.
Direct-family selection and selected-address candidate scans remain separate
follow-up work; this removal does not establish the whole-call fast bound.

For remaining coverage, hold the callee contract/effect fixed and grow
distinct direct families and selected-address candidates. Measure call
preparation, execution and completion together; retain opaque-body and
refusal coverage. Coordinate with [Scaling](scaling.md), cause 3, without duplicating its
implementation work or changing its priority here.

### Statement-exit fact transport — boundary and remaining coverage

Statement result publication now has a test-build discovery guard. Condition
fact transport is registered as discovery, including its formerly unregistered
"direct" route. Call-result/postcondition integration coverage and an adversarial
guard test prevent that helper from silently returning to publication. The
removed adapter's lower-level red diagnostic is retired: it measured a helper
that publication no longer calls, not the cost of the operation after removal.

This does not guard all statement preparation. Other cell-map/effect searches,
transport re-validation, ownership validation, loan access, and composite
framing remain separately scoped candidates. Keep ordinary obligation solving
on the driver and optional fact discovery in expandable search; a missing
bonus fact is not a new mandatory obligation.

### M1: reads, caches and history — coverage gaps

The [memory-history roadmap](fact-aware-frame-walks.md) names read-side
`CellsForgotten` projections and bulk-write preparation. Inspect
`CMemory::prepare_store_cache`, its callers, and bounded cell-source queries
separately. A derivation edge named `CellsForgotten` does not itself establish
an unbounded history search: the inspected cell-source route counts real hops
against `max_hops` and gates its extended bridge.

Keep the read/store/explicit transport fixed while growing prior states,
cached cells, compact runs and holes independently. Measure cold misses and
repeated adjacent/non-adjacent reads; grow genuinely overwritten pieces as a
separate output-sized control. Retain exact typed-read identity, initialization,
partial overwrite, freed-pointee and provenance refusals. New primitive designs
belong in the design/build discussion, not this audit pass.

### J1: branches and loops — coverage gap

`interface_abstraction_work_scales_with_unrelated_locals_and_memory` currently
allows up to 3x charged work when stable state doubles. It is a loose growth
check, not evidence that a fixed one-local change ignores ambient state.
`abstract_c_state_for_interface_join_across` already uses persistent differences
for parts of this operation; do not infer a scan just from the weak assertion.
The `JoinLocals::Stable` loop-head policy has different traversal behavior.

Measure the complete split/join and loop entry/exit at fixed arms, changed
locals and interface size, growing stable locals/cells/resources and prior
joins. Separately grow explicit arms, changed entries and invariant text.
Classify retained-state traversal against these actual inputs and changes;
exclude unavoidable explicit path enumeration from the ambient test.

### E1 and Q1: logical steps and evidence lifecycle — deferred evidence/gaps

[Scaling](scaling.md), cause 4, records repeated execution, result revalidation
and completion work. That description includes historical fixes and requires
caller-by-caller reconciliation before it is a current defect list. The completed preparation controls include
`prepared_call_obligations_execute_once_as_contract_and_context_grow`, named,
population/authority and return-fold construction, and the former failed/legacy
retry routes. All twelve selected controls passed at the reconciliation baseline.
Do not count these as still-unfixed repeated execution; they do not settle
condition/function theorem contexts, observation producers, or all joins and
final publication.
Count executor invocations and producer/result comparisons through complete
explicit steps, rewrites, joins and final publication, including uncharged
work. Reuse checked producer results rather than introducing another checker.

[Deep quantifier scaling](deep-quantifier-scaling.md) records repeated nested
`Integer` binder freshening. `freshen_integer_forall_body` still collects body
variables and substitutes when a binder collides; its non-collision shortcut
must be measured separately. Rebuild a complete nested-introduction curve with
and without ambient binder collisions. Old helper counts are historical, not
current complete-operation results. Preserve capture avoidance and expansion.
Both linked items retain their existing deferrals; the general constant-ish
checking claim must disclose them until resolved.

## Prevention coverage

`kernel::search::SearchPermission` gates ambient fact discovery, and
`build_support/search_boundary.rs` rejects selected forbidden calls and
iterator patterns. These guards cover named APIs/functions, not arbitrary
Rust iteration, allocation or structural comparison. `CheckingWorkScope`
attributes charged work inside selected helpers independently of enclosing
search. It does not establish coverage of every checker or detect uncharged
work. Operation closure therefore needs both a source-boundary argument and
complete-operation scaling controls; neither mechanism alone proves the rule.

## Next design/build cycle and completion

The behavior-preserving architectural split is described in
[Separate proof operations from proof search](../design/proof-operations-and-search.md).
Use its frozen dependency inventory to remove operation-to-search calls one
route at a time. Mixed callers now have semantic classifications; no strict search-free
execution guarantee is claimed. The measurements below feed that migration.

Choose one of these slices for the next design/build cycle; this audit does not
authorize a new primitive or a verifier behavior change.

| Candidate | First concrete step | What completing it would establish |
| --- | --- | --- |
| Boundary enforcement / interface cleanup | Extend the theorem-operation discovery guard to the next audited primitive, identifying existing exceptions before enforcing it. The inventoried search/support adapters have been extracted. | Clear ownership of discovery; guards must distinguish allowed driver solve from search inside primitives, even when invoked by solve. No claim to detect arbitrary loops. |
| Arithmetic obligation generation | Reduce one operator's inline safety decision; reproduce the spelling and position-drift controls above before designing a retained result plus obligation. | That operator generates and publishes bounded work while the driver alone solves its safety goal; no promise to migrate all arithmetic in one patch. |
| L1 active-loan write | Fix one write and owner, grow aliases with one active loan, then symbolic loans with fixed aliases. Write the complete-operation red scaling test first. | Evidence of a concrete remaining scan, or a closed coverage gap if flat. Choose an index or explicit-proof repair only after the result. |

F2 and C1 remain subsequent measurement candidates, followed by R2, R1
reachability, and J1/M1/lifecycle coverage. Declaration-validation search and
legacy explicit transport remains a separate design track; preparation completion did
not remove either. The inventoried operation/driver adapters have been extracted. This clears
that migration list; it does not remove the direct operation/search dependencies
or prove that all generated operations are fast.

For whichever slice is selected:

1. For each operation, retain source caller, input/delta definition, independent
   ambient axes, multi-size deterministic results, cold/repeated failures,
   semantic controls, and the checking/search boundary. Fix a complete route;
   do not mark the operation done because a common special case is flat.
2. Add source-level integration controls as well as helper tests. An expanded
   proof must replay without search. Attribute excessive checking to checking,
   even inside `solve`; `CheckingWorkScope` currently covers selected helpers,
   not every operation. Audit uncharged loops and deep comparisons as well as
   charged counters. No budget increase or warm cache substitutes for a bound.
3. Reconcile the adjacent roadmap items and fill the operation coverage gaps
   before claiming the general principle. Removing the named loops alone is
   insufficient. Keep this document an inventory of remaining evidence/work,
   not a history of completed PRs; move durable guarantees to the efficiency
   documentation and retain their tests when rows are resolved.

Persistent branches retain their parent contexts. Proof repairs preserve the
original C and contracts, using explicit separation and ordinary preservation/equality steps
at exact footprint entry/exit states. Whole-region preservation must be
explicit composition, not a hidden transition walk. Inconclusive checking
cannot establish equality or preservation, and explicit proof application must
not reconstruct identities or search for intermediate states.

