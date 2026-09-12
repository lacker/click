# P1: Unify memory and other resources across contracts and callbacks

## Objective and violated invariant

Memory is a primitive resource family inside the general resource system.
Contracts, resource transfer, framing, observation, and callback application
must use that system consistently. Packaging memory in a declared resource
must not break an otherwise expressible contract merely because different
implementation paths evaluate its ownership, dependent addresses, or effects.
Explicit fold/unfold steps may still be necessary to cross an abstraction.

This is a language-preserving implementation project, requested on 2026-09-11.
It covers the internal refactorings and existing-semantics bug fixes described
below, not new resource capabilities. P1 is explicit: the dependent footprints
and repeated augmentation callbacks overlap the MVR blockers in
[function-contracts.md](function-contracts.md), G1 through G3.

Success means one checked account of a contract's resource transition, with
memory-specific behavior supplied by the memory family and its effect
projection. Merely renaming enums, adding a common wrapper around divergent
implementations, or making one callback fixture pass is insufficient.

## Evidence and current implementation map

Planning inspection used base `fe1ef83a4ee0b6bd2541b94000459cde6d6676ea`.
The G1-G3 failures below were documented by the existing callback issue; they
were not independently reproduced while writing this plan. Worker W0 must
check the current base before classifying them as still failing. Source
locations are navigation hints; follow symbols if files have moved.

- `src/kernel/primitives.rs`: `CResourceFact` owns or views a `CResource`;
  memory, composites, tokens, and exclusive instances share `ResourceContext`.
  `ResourceFamilyAlgebra` supplies entailment, consumption, residuals,
  normalization, and cores. Keep this real common boundary.
- `src/kernel/primitives/resource_algebra.rs`: family implementations and
  indexed resource storage, including supported projections. Memory has
  specialized range entailment and read/write authority. Exclusive instances
  have no viewed core; tokens/composites have different quantity rules.
- `CResourceSpec` and surface `ResourceClause` use dedicated owned/viewed
  memory variants, while declared-resource variants carry an access mode.
  This duplicates generic clause handling above the family algebra.
- `CFunction` stores resource preconditions, returns, borrowed-return indices,
  pure clauses, and `contract_mutable` separately. `CFunctionContract` embeds
  a `CFunction` template whose name and body are not the callback target.
- `src/surface/lowering/annotations.rs`:
  `collect_owned_resource_memory_segments` traverses resource definitions to
  construct a separate memory footprint; `annotated_function` installs the
  resource summary and contract summary through separate paths.
- `src/surface/proof.rs`: `initial_claim_context` materializes/projects
  resources and establishes entry facts. `src/surface/verification.rs`:
  `build_function_environment` prepares named contracts through that path.
- `src/kernel/functions.rs`: `execute_verified_function_templates`,
  `prepare_function_resource_transfer`, `evaluate_function_resource_context`,
  `evaluate_function_return_resource_context`, and refinement preparation
  already share substantial machinery. Consolidate remaining differences;
  do not build a second call engine.
- Return evaluation intentionally distinguishes borrowed entry-selected
  resources from exclusive instances with post-call fields. Binder transport
  and contract substitution have their own adaptation paths.

Existing positive witnesses include:

- `mdtests/c_contract_executes_buffer.md`: unfold a `Buffer`, call through
  `Raw`, and fold it to establish `Buffered` for the same callback.
- `mdtests/c_named_function_contract_frames_folded_composite.md`: keep an
  unrelated folded bundle in the callback frame.
- `mdtests/c_named_function_contract_borrows_abstract_token.md`: borrow an
  owned token through a callback and consume it afterward.
- `mdtests/c_contract_executes_counter_forward.md`: transport a chosen
  exclusive instance while preserving another instance in the frame.

## W0 baseline and handoff (2026-09-11)

W0 started from `188a594b` (`Plan P1 memory and resource contract
unification`). The checkout was clean. No source, C, budget, quarantine, or
unrelated changes were made. The positive witnesses on this base pass under
the ordinary bounded mdtest runner:

```text
MDTEST_FILTER=rb_augment_callbacks_helper cargo nextest run --test mdtests --no-capture
  PASS (1/1, 0.091s)
MDTEST_FILTER=augment_rotate_callback.md cargo nextest run --test mdtests --no-capture
  PASS (1/1, 1.231s)
MDTEST_FILTER=augment_rotate_model_callback.md cargo nextest run --test mdtests --no-capture
  PASS (1/1, 0.295s)
```

The following are fresh, temporary reductions in the W0 worktree; they were
removed and are not tests or acceptance substitutes. They preserve the C
source and use the normal `cargo nextest` deterministic-work bounds.

- **G1:** changing the three callback contract footprints in
  `rb_augment_callbacks_helper.md` from `views` to `owns` while leaving the
  caller's `views parent->left/right` gives status 100 and
  `step() produced runtime error: missing resource fact owns node[...]`.
  Giving the caller `owns parent->left/right` makes the failure the callback
  lookup itself: with `Propagate` still `views` and `Copy`/`Rotate` changed to
  `owns`, the exact command
  `MDTEST_FILTER=rb_augment_callbacks_helper cargo nextest run --test mdtests --no-capture`
  gives status 100 at the second indirect call, through
  ``__click_call_result2``: `no matching named contract is available for this
  value`. Changing all three callbacks to `owns` fails earlier at
  ``__click_call_result1``. Thus the current base confirms the G1 family, but
  the exact failing call number depends on which footprints are made owned;
  the issue's three-call target remains unimplemented.
- **G2:** a temporary two-clause function with
  `owns pair(node)` followed by `owns node->right->augmented` (where `pair`
  owns `node->left` and `node->right`) was run with
  `MDTEST_FILTER=_mvr_g2 cargo nextest run --test mdtests --no-capture`.
  Status 100 was the certification diagnostic
  `could not certify contract for f: could not evaluate the contract entry
  resources: could not evaluate an owned memory resource segment (resource
  clause 2 of 2)`. This is an independent reduction of the dependent-base
  failure, not a claim that the existing rotation workaround passes the
  natural contract.
- **G3:** adding `requires old->left != 0; views old->left->augmented` to the
  named `AugmentRotate` contract in the rotation fixture, then running
  `MDTEST_FILTER=augment_rotate_callback.md cargo nextest run --test mdtests --no-capture`,
  gave status 100 while preparing the contract:
  `could not prepare named contract AugmentRotate: missing pure fact:
  loadable(base=old, bytes=8)`, with no pure or resource facts available.

During this investigation `origin/master` advanced through
`16fe83e4` (`Name a retained cell's load by the value it already holds`),
which directly fixes G1. Its three new real-footprint witnesses are green on
the integrated latest checkout (`f4f76f5c`, which contains that commit and
the subsequent G1 status update `4597941b`):

```text
MDTEST_FILTER=rb_augment_callbacks_helper_owns cargo nextest run --test mdtests --no-capture
  PASS (1/1, 0.163s)
```

The paired cell-level separation witness also passes, while
`rb_augment_callbacks_helper_owns_rejects_unseparated.md` still rejects the
same proof at the second call. The commit's rationale identifies the changed
load naming across call havoc: retained table cells now resolve to the value
they already hold, so the opened callback fact remains tied to the reloaded
pointer. Therefore G1 is **fixed upstream and must not be reimplemented**;
W5 should preserve these witnesses and focus on R3's permitted-mutation and
support-provenance cases. G2 and G3 were not touched by `16fe83e4` and remain
open pending a recheck from the manager's latest integrated base.

The starting-base G1 reductions showed a verified failure, not a performance
or search-budget issue; the upstream fix is now independently green as noted
above. G2 is a verified certification/evaluation failure. G3 is a verified
named-contract lowering failure. No root cause beyond those observed
boundaries is assumed here: in particular, callback-fact provenance loss is a
W5 hypothesis until R3 is reduced with an actual permitted mutation.

### W0 ownership map for R1-R6

| Regression | Reusable positive witnesses and next minimal case | Paired rejection/preservation case | Owning chunk |
| --- | --- | --- | --- |
| R1 | Start from the existing folded-composite/frame witnesses. Add the smallest direct function whose `owns pair(node)` supplies a guarded link load for a separate `owns node->right->augmented`; then use the natural rotation only after this passes. | Omit the link-read authority or nonnull guard; overlapping owned pieces must not be accepted. | W3 |
| R2 | Reuse `c_named_function_contract_*` callback fixtures, `c_contract_executes_*` theorem fixtures, and the direct R1 reduction. Run the same authorized dependent clause through named callback application, explicit execution, automatic formation, and certification. | Missing access/guard remains an obligation; automatic formation stays bounded and exact. | W3, with W2 interface coverage |
| R3 | Begin with `rb_augment_callbacks_helper.md`: one scoped open, three callback fields, owned `node->left` footprints, and unchanged guarantees. Add one bounded helper where one callback performs an allowed mutation. | A changed supporting table cell or consumed support invalidates the old callback fact; unrelated framed support survives. | W5 |
| R4 | `c_contract_executes_buffer.md` is the raw/one-layer `Buffer` unfold/call/fold witness. Frame an unrelated cell and token, then compare raw and wrapped checked effects. | Out-of-authority write and view-to-own conversion fail. | W4 |
| R5 | Use the existing return-indexed and counter-forward fixtures for entry-selected borrowed ranges and exclusive identity. Add a pointer-field change with an owned range and a returned instance whose fields are constrained only by its guarantees. | No retargeting of an `owns` range, invented field preservation, or aliasing of two instance identities. | W4 (memory), W6 (instances/binders) |
| R6 | `c_named_function_contract_borrows_abstract_token.md`, `c_named_function_contract_borrows_folded_composite.md`, and the frame theorem cover scoped callback borrows and unrelated frames. | Double token consumption fails; persistent aliases retain current deallocation restrictions and scoped views do not escape. | W5 |

### W0 path trace and proposed internal boundaries

The current implementation has one useful family boundary but several
contract/transition entry paths around it. `ResourceFamilyAlgebra` in
`src/kernel/primitives.rs` and `resource_algebra.rs` is the real common
boundary: memory supplies range splitting/read authority, composites and
tokens use exact quantities, and instances enforce identity/exclusivity.
W1 should preserve that specialization while normalizing the surface
specification above it.

| Path | Current entry and duplicated preparation | Narrow boundary for W1-W6 |
| --- | --- | --- |
| Direct verified C call | `execute_c_function_call_paths` dispatches a verified rule or body; `prepare_verified_function_call` separately binds arguments, evaluates `resource_requires`, calls `prepare_function_resource_transfer`, lowers contract requirements, and later evaluates returns. | W2 supplies one body-independent contract interface; W3 supplies a dependency-aware clause elaboration result (term plus checked load/guard obligations); W4 consumes one transition record for transfer, effects, and return. |
| Named callback call | `execute_c_function_contracts_paths` selects a `CFunctionContract`, optionally builds `ResourceCallApplication`, then re-enters `execute_verified_function_templates` and the same `prepare_verified_function_call`; exact pointer `Contract(p)` facts are checked by `function_contract_requirement_is_proven`. | W1's normalized resource terms and W2's interface are shared with direct calls. The callback fact remains an exact-pointer evidence input; W5 owns support/provenance invalidation, not a global retention list. |
| Explicit execution theorem | `surface/proof/pure_theorems/execution_theorems.rs::verify_execution_theorem` rewrites the target clauses and builds a one-call block, then uses grouped checked execution and `prove_c_function_contract_execution_paths_with_checked_artifacts_and_pure_theorems`; concrete targets use ordinary C, abstract targets use source contracts. | W2/W6 provide the same contract/binder instantiation; W4 receives the same checked transition. The theorem's closed checked artifact remains distinct authority from a verified body or external assumption. |
| Automatic formation | `function_refines_named_contract` calls `prepare_automatic_contract_refinement_context`, then `function_refines_named_contract_in_case`; concrete pointer formation is accepted only for a verified/external exact target and compatible vocabulary/effects. | W2 owns the body-independent relation; W3 supplies checked entry/post clause obligations; W6 supplies identity-based binder maps. Keep bounded candidate applicability and exact/forced pairing. |
| Contract certification | `verification.rs::build_function_environment` prepares named contracts through `initial_claim_context` and `annotated_function`. Function certification constructs a fresh entry context, invokes checked artifacts through `prove_c_function_contract_execution_paths_with_checked_artifacts_and_pure_theorems`, then claims are finalized in `kernel/api/contract_certification/contract_claims.rs`. | W1/W3 must make named and ordinary entry lowering agree. W4's transition/effect projection is the sole checked footprint source. Certification may reuse checked artifacts, but must not rerun a concrete body or turn pending obligations into authority. |

The resource/effect duplication to remove or make read-only is now pinned:
`function_contract_summary` in `annotations.rs` separately traverses owned
resource definitions through `collect_owned_resource_memory_segments`, while
the kernel separately evaluates `CResourceSpec` through
`evaluate_function_resource_context` and computes transfer/return effects in
`prepare_function_resource_transfer`, `evaluate_function_return_resource_context`,
and `evaluate_contract_mutable_ranges`. `initial_claim_context` additionally
materializes/project resources and facts before `annotated_function` installs
the resource and contract summaries. W4 should make its transition projection
authoritative and leave any retained surface traversal as a checked,
read-only artifact consumer.

Authority and obligations should cross the proposed boundaries as follows:
W1 lowers syntax to a resource term plus explicit access/role/snapshot metadata
and delegates family validity to the existing algebra; W2 instantiates one
contract interface without conflating body evidence, external assumptions, or
pointer-specific callback facts; W3 returns symbolic terms together with
load/bounds/guard obligations and never assumes a contract's own postcondition
at entry; W4 consumes those checked obligations to produce one transition
record (borrowed entry resources, consumed residuals, frame, post outputs, and
effect projection); W5 attaches observations to support/version/scope and
invalidates them on support changes; W6 transports semantic instance identity
separately from spelling and snapshot state. This keeps unresolved obligations
as obligations at both ordinary and callback calls.

W0 changed only this issue document. The resulting checkpoint is ready for
manager integration; no old implementation path or adapter was removed.

## W1 handoff (2026-09-11)

W1 started from `345eb056` (`Reconcile memory resource issue with G1
status`) in the isolated `codex/mvr-w1` worktree. The normalized resource
specification is now a validated `CResourceSpec` carrying a `CResourceTerm`,
explicit access, quantity, transfer role, and snapshot. Memory remains a
range term; composite, token, and field-bearing instance terms retain their
family-specific identity and validation. Surface resource lowering constructs
this form at one metadata-aware boundary, and substitution, interface
identity, termination, loop handling, proof execution, certification, and
resource evaluation consume it without legacy variant matches or the removed
borrowed-ensure index. No syntax, C source, budget, quarantine, or unrelated
files changed.

The focused normalized-resource tests cover memory/composite/token/instance
families, valid view/own/count combinations, rejected memory quantities,
rejected counted views, rejected instance views and non-composite instance
bodies, and indexed lookup scaling at sizes 16, 32, 64, and 128. The
deterministic-work ratio assertion passed. Existing resource, contract, heap,
surface, callback, expansion, certification, and rejection tests retain their
outcomes. The follow-up review makes the normalized carrier fields private;
interface normalization and substitutions rebuild through `CResourceSpec::new`,
while instance-inner reconstruction reports an explicit contract error if its
validated invariant is ever violated. A focused regression checks substituted
quantity/term metadata, instance-inner access/quantity/role/snapshot metadata,
and public rejection of an invalid instance view.

Checks in the W1 worktree all passed: `cargo check --all-targets` (0),
`MDTEST_FILTER=resource cargo nextest run --test mdtests --no-capture` (0),
`cargo nextest run --lib resource_tests contract_execution_tests heap_tests`
(172/172), `cargo fmt --check` and `git diff --check` (0), and the unfiltered
`scripts/check.sh` gate (0; 2556 tests plus the 14 fixture/example checks).
The tested W1 implementation is committed as `69fdd385`; this follow-up
review hardens its construction boundary and is recorded in the separate
fixup commit following it. The manager should integrate both commits without
merging or pushing from this worktree. No verified blockers remain; G2/G3 and
later R1-R6 behavior remain assigned to later chunks.

Final integration note (2026-09-11): this reviewed W1 pair was applied onto
`42b8b6eb` after upstream's whole-contract resource supply and centralized
unaddressable-clause diagnostics landed in `53948479` and `7e55fdc7`. The
resulting commits are `ef44ad20` and `d8d1db47`. Their only merge conflict was
resolved in favor of W1's normalized, validated `CResourceTerm`/`CResourceSpec`
carrier while retaining upstream's dependency-aware whole-clause evaluation,
current issue findings, and dedicated instance-rename representation. This
integration does not duplicate or revert the upstream whole-contract algorithm;
the branch remains unmerged and unpushed for manager integration.

## Language-preservation contract

Every worker must preserve the following. A proposal that needs a different
rule is outside this issue and must be reported to the manager/user, not
silently included.

1. Keep existing Click syntax, resource declarations, tactic forms, and C
   source unchanged. Fixing a verifier bug may make an existing, valid contract
   verify; strengthening regression sidecars to exercise real footprints is
   allowed. Do not rewrite C to accommodate the verifier.
2. `views` remains read-only. Ownership may satisfy a view through a checked
   core where that family supports it. A call-scoped borrow does not mint a
   persistent caller view. Existing persistent views retain their current
   lifetime/deallocation restrictions.
3. `owns` returns the resource selected at entry. In particular, changing a
   pointer field does not retarget a borrowed memory range at return.
   Exclusive instances retain their identity and acquire post-call fields
   constrained only by guarantees; ownership alone does not freeze fields.
4. `consumes` transfers owned authority without an implicit return;
   `produces` describes returned authority at the appropriate post-state,
   including contracts indexed by `result`. Produced ownership is not proof
   of allocation freshness.
5. Memory range splitting, token/composite quantities, instance exclusivity,
   allocation authority, guarded recursion, and existing population rules
   remain distinct family semantics. A common representation does not make
   every operation valid for every family.
6. Loads/stores still require appropriate authority, with existing local and
   read-only storage rules. Owning a wrapper must not expose its body for
   arbitrary proof steps without the currently required fold/unfold/open or
   observation operation. Internal effect queries are not public unfolding.
7. All finite writes stay within the checked effect footprint, even on paths
   that do not return. Preserve memory outside the footprint only with checked
   frame evidence, including address dependencies for dependent loads.
8. Automatic callback formation remains bounded and exact; explicit execution
   theorems remain the escape hatch. Do not broaden smart search or weaken
   refinement checks to hide a representation problem.
9. Preserve source-level expansion, checked proof provenance, independent
   contract certification, and the no-body-rerun ratchet. Pending or failed
   obligations must never become successful authority through a cache.

Explicitly excluded: views of field-bearing instances; new memory instance
binders/proof parameters; a new `memory(...)` spelling; selectable resource
capability syntax; fractional permissions; dynamic footprints for counted
populations currently restricted to stable footprints; new recursion forms;
more permissive binder inference; and unrelated prover completeness work.
General snapshot and transition machinery may accommodate future extensions,
but this issue must not enable them.

## Findings from the function-contracts close-out (2026-09-11)

- Resource clauses now read what the whole clause set supplies, including
  cells inside a folded composite, for memory segment bases (`7e55fdc7`,
  `mdtests/contract_owns_through_composite_field.md`). A composite
  *argument* that needs a load is still refused on the surface before that
  evaluation runs: `owns pair(node->left->left)` fails with ``could not lower
  resource `pair` argument 0: missing pure fact: loadable(...)``. The same
  whole-clause-set rule should apply to composite arguments.
- The surface check that refuses an unaddressable clause and the kernel
  evaluator now share one wording (`resource_clause_position_note` /
  `resource_clause_stall_note`), but the surface counts surface clauses while
  the kernel counts lowered `CResourceSpec`s. They agree on every fixture; a
  `MemoryAggregate` clause that lowers to several specs could number them
  differently. Unify the count when either side is next touched.
- Named contracts never reach `evaluate_function_resource_context`, so the
  surface check in `initial_claim_context` is the only thing refusing a named
  contract's unheld link read (`mdtests/named_contract_rejects_unheld_link_read.md`).
  Routing named-contract clauses through the kernel evaluator would make the
  kernel the single source of truth.

## Small intended regressions

These are behavioral targets, not permission to commit failing default tests.
Reduce against fixed C and use existing proof operations. The missing-access
variants must actually lack access from every other resource in the context.

| ID | Positive regression | Paired rejection/preservation check |
| --- | --- | --- |
| R1 | `owns pair(node)` supplies the link needed to evaluate a separate `owns node->right->augmented`, with a proved nonnull guard; verify the direct function and its opaque caller. | Without link-read authority or the required guard, fail locally; overlapping owned pieces cannot create double authority. |
| R2 | The same dependent clause works in a named callback contract and explicit callback execution theorem, using the same authorized entry context. | An unproved access obligation or guard cannot authorize a callback or its effects. Automatic formation is tested only within its existing admitted fragment. |
| R3 | Open one augmentation suite, invoke its three callback fields with owned footprints, and close it; preserve the suite's callback facts when their support is unaffected. | If a call can change the supporting table cell or consumes its support, the old loaded pointer's fact cannot justify a newly loaded callback value without proof. |
| R4 | Raw memory and a one-layer `Buffer` wrapper have the same checked effects when connected by explicit unfold/call/fold. Frame an unrelated memory cell and token. | Writing outside the wrapper's authority, or converting a view into ownership, fails. |
| R5 | An `owns` range based on a pointer field returns the entry-selected range after the field changes; a returned exclusive instance has the same identity and suitably fresh fields. | No implicit retargeting, no invented field preservation, no aliasing two instance identities through a binder map. |
| R6 | A callback borrows an owned token or memory view without adding a persistent caller view; an unrelated framed resource survives. | Consuming the token twice fails; a real persistent alias still blocks deallocation as required today. |

Start R3 from `mdtests/rb_augment_callbacks_helper.md` and G1: use
`owns node->left` plus `ensures node->left == old(node->left)` for each
callback as the smallest footprint regression. Also retain a bounded case
with an actual permitted mutation so the fix does not rely on every write
being described as unchanged. Use the rotation fixtures for R1/R2 only after
the small cases pass; do not begin by expanding the full Linux proof.

## Dispatch rules and dependency order

The chunks below are work assignments inside this single issue. Do not create
one issue file per chunk. One worker owns each chunk; the manager records its
base commit, completion commit, gates, remaining blockers, and next assignment
in the handoff. Read root `AGENTS.md` before dispatch.

Default order is **W0 -> W1 -> W2 -> W3 -> W4 -> W5 -> W6 -> W7**.
This intentionally serializes changes to `src/kernel/functions.rs`, the
primitive types, and surface lowering. Do not give two implementation workers
those shared files concurrently. W6 logically needs W2 and can move earlier
only if the manager explicitly reschedules its exclusive file ownership.
Read-only review or preparation of disjoint fixtures may run in parallel;
do not merge tests asserting new success until their implementation is green.

Each implementation worker uses a dedicated branch/worktree, begins from the
latest integrated green predecessor, and delivers a coherent tested commit.
No worker may integrate a failed prototype or overwrite another worker's
changes. If a prerequisite exposes a tooling failure, reduce/fix it first or
return a green checkpoint with a blocker report. Do not raise budgets or add
quarantines to satisfy this plan.

### W0 — Establish the baseline and freeze the compatibility matrix

**Dependencies:** none. **Owner scope:** investigation, focused regression
design, and status/links in this document; no architectural changes.

Tasks:

- Reproduce G1-G3 on the current base under ordinary bounded verification.
  Record exact commands, fixture/reduction, diagnostic, and whether the gap
  still exists. If already fixed, identify its passing regression and preserve
  it; do not implement an obsolete diagnosis.
- Trace direct call, named callback, explicit execution theorem, automatic
  formation, and certification entry paths. Identify where resource terms,
  access obligations, effects, and binder maps are constructed more than once.
- For R1-R6, identify reusable positive and negative tests. Record which new
  minimal cases each later worker must deliver. Pin the semantic distinctions
  in the language-preservation contract above, especially return snapshots.
- Propose narrow internal API boundaries for W1-W6, with caller migration
  lists. Explain how authority and obligations pass each boundary.

**Done:** a concrete baseline/handoff and regression ownership map exist;
documented failures are distinguished from fresh observations. Any committed
tests pass under their honest current expectation. A temporary expected-failure
reproduction must be switched to success by its fixing chunk, not left as an
acceptance substitute. No failing default fixture or speculative root-cause
claim is committed.

### W1 — Normalize resource specifications above the family algebra

**Dependencies:** W0. **Primary files:** `src/kernel/primitives.rs`,
`src/kernel/primitives/resource_algebra.rs`, surface resource lowering,
resource spec evaluation and substitution callers.

Tasks:

- Introduce a normalized internal specification that separates the resource
  term from access mode. Keep transfer role (borrow/consume/produce), quantity,
  binder identity, and snapshot selection explicit rather than encoding them
  through memory-only variants or incidental vector positions.
- Keep a memory-range term and specialized memory-family implementation.
  Validate quantities and permitted access by family; do not accept a memory
  quantity or an instance view merely because the representation can hold it.
- Lower existing syntax to this form at a single boundary. Migrate all
  consumers of the replaced forms, including substitution, diagnostics,
  formatting/expansion, equality/identity, and certification. Temporary
  adapters must have a named removal owner, no independent semantic behavior,
  and be removed before W7 completes.
- Preserve indexed lookup and shallow/persistent identities. Do not replace
  efficient memory indexes with a generic scan or a deep term comparison.

**Tests/done:** existing resource and contract tests retain their outcomes;
focused tests cover all supported families, accesses, and rejected quantity
forms. Surface round-tripping/expansion stays unchanged. Add deterministic
multi-size coverage for any changed hot representation in this chunk.

### W2 — Extract one contract interface and share application preparation

**Dependencies:** W1. **Primary files:** contract primitives and APIs,
`src/kernel/functions.rs`, `src/kernel/api/contract_certification*`,
`src/surface/verification.rs`, `src/surface/lowering/annotations.rs`.

Tasks:

- Represent the contract independently of a concrete C body: typed runtime
  parameters/result, proof binders, pure pre/postconditions, resource clauses,
  snapshot/return roles, and checked effect information. Preserve source
  provenance for diagnostics. The precise Rust type name is not prescribed.
- Have concrete verified functions, external assumptions, named callback
  contracts, and execution theorems reference this representation. Keep their
  evidence distinct: an external assumption is not a verified body, and a
  callback fact is tied to its exact pointer value.
- Share contract instantiation/preparation across ordinary and callback calls,
  refinement, and certification where their judgments coincide. Do not merge
  distinct soundness checks just to reduce code size.
- Preserve snapshot meaning, contract identity, parameter coercion, binder
  selection, bounded candidate applicability, and complete checked artifacts.
  Avoid hidden execution of a concrete body when applying its summary.

**Tests/done:** direct/callback versions of existing memory, token, composite,
and instance contracts agree on resource transitions. Existing rejection
tests for wrong callback values, unverified targets, and invalid refinements
pass. No independent legacy contract evaluator remains behind the new type;
any intentionally distinct rule is documented. Deterministic work tests cover
repeated small calls with growing unrelated resources/functions.

### W3 — Elaborate dependent clauses with checked access obligations

**Dependencies:** W2. **Primary files:** entry-context preparation in
`src/surface/proof.rs`, contract/resource lowering, contract evaluation,
kernel resource evaluation, and corresponding certification preparation.

Tasks:

- Separate constructing a symbolic resource/address expression from proving
  the loads, bounds, guards, and arithmetic that make it well-defined.
  Share this preparation between direct and named contracts.
- Establish the available entry resources and pure requirements through
  explicit dependencies. An owned folded composite may support the checked
  observation needed to evaluate a dependent clause without becoming free
  mutable body authority in the user's proof state.
- At function entry, distinguish assumed preconditions from the obligations a
  caller must discharge. At a call, unresolved obligations remain obligations;
  they cannot be mistaken for established applicability of another callback
  candidate. Do not use the contract's own postcondition as entry evidence.
- Use a bounded dependency worklist or equivalent incremental mechanism;
  avoid repeated whole-context fixed-point scans. Preserve lexical binder
  scope. This is not permission for forward references or a new contract
  clause-ordering language rule.
- Report unresolved/circular access dependencies with the source clause and
  missing authority/guard. Do not manufacture loadability or dump raw states.

**Tests/done:** R1 and R2 pass in direct verification, opaque calls, named
contracts, execution theorems, and certification as applicable. Negative
variants retain missing-authority/guard failures. Test several authorized
dependency depths and independent clauses; charge work to the dependency
nodes/edges, with four-size deterministic curves. Update G2/G3 status in the
existing callback issue only after the regressions and gates pass.

### W4 — Make resource transitions authoritative for memory effects

**Dependencies:** W3. **Primary files:** call transfer/return evaluation,
memory havoc/frame checks, footprint lowering, contract certification and
refinement effect checks.

Tasks:

- Prepare one checked transition identifying borrowed inputs, consumed inputs,
  caller residuals/frame, and post-state outputs. Tie each evaluated resource
  to the correct snapshot and evidence; use that information consistently in
  call application and return checking.
- Derive the memory write footprint through a single authoritative projection
  of that transition and the relevant resource definitions. Opaque tokens
  contribute no memory authority; wrappers contribute only the authorized
  body effects; instance body queries must respect their identity/state.
- Route havoc, finite-write checks, refinement containment, and certification
  through this projection. A stored footprint is allowed as a checked derived
  artifact, not as a second independently reconstructed specification.
- Preserve guarded/subrange behavior, read-only rejection, allocation lifetime,
  and outside-footprint framing, including loads used to compute addresses.
  Preserve existing supported recursive representations without eagerly
  unfolding an unbounded resource. Keep dynamic population footprints rejected.
- Remove duplicate surface/kernel footprint traversal when migration is done,
  or identify the one remaining derivation and its read-only consumers. Do not
  silently widen a footprint when exact projection is unavailable.

**Tests/done:** R4 and the memory half of R5 pass, together with current
guarded-footprint, overlap, read-only, deallocation, and return-indexed tests.
An out-of-footprint store on a non-returning path remains rejected. Add
four-size deterministic curves for fixed calls with growing unrelated frames
and for growing explicitly used wrapper members. Certification and expansion
agree with ordinary verification.

### W5 — Preserve resource observations and scoped borrows by provenance

**Dependencies:** W4. **Primary files:** supported resource projections,
pure-fact/snapshot transport, scoped open/close and resource proof steps,
callback-fact lookup, and call successor construction.

Tasks:

- Reproduce R3 and locate the actual loss or misuse of authority before choosing
  a representation fix. Treat provenance loss as a hypothesis, not a proven
  diagnosis from this plan.
- Reuse/extend existing support records so an observation identifies its
  supporting resource, relevant memory/instance version, and scope. Do this
  consistently for memory observations, composite facts, and loaded callback
  contract facts; do not add an unconditional callback-fact retention list.
- Preserve observations whose support is framed through a call. Invalidate or
  reestablish them when supporting ownership/state changes. An unchanged
  support must not disappear merely because an unrelated owned range changes.
- Ensure close restores the required representation once, without duplicating
  authority or retaining an expired scoped view. Preserve current persistent
  view behavior and kernel checking of proof-recorded resource operations.

**Tests/done:** R3 and R6 pass, including actual permitted mutations, expired
support, changed table cells, and unrelated frames. The three-call helper uses
one scoped open with owned footprints and no artificial C changes. Add
deterministic curves varying calls and unrelated supported facts independently.
Update G1 status only after these tests and the full gate pass.

### W6 — Unify existing binder transport and snapshot substitution

**Dependencies:** W2 logically; default dispatch after W5 to avoid conflicts.
**Primary files:** contract substitution/environment lowering, existing parser
binder metadata, call binder selection, resource-instance return evaluation,
and refinement parameter maps.

Tasks:

- Use one internal binder map for the already-supported direct-call,
  named-contract, and execution-theorem forms. Keep binder spelling separate
  from semantic identity, with declaration metadata as the authoritative source.
- Replace the field-free `ResourceField` substitution trick for instance
  renaming with a dedicated internal identity-substitution operation. Audit
  capture avoidance, nested bindings, and entry/post-state projections.
- Remove redundant parser-side semantic registries once all existing callers
  use declaration metadata. Preserve supported source spelling and current
  output-binder limits; adding new surface forms is not this assignment.
- Preserve exact/forced automatic pairing and existing ambiguity refusals.
  Do not make field values identify instances, infer new same-family pairings,
  or preserve fields that the contract leaves unconstrained.

**Tests/done:** R5's instance half passes; existing direct-call binder transport,
`as` maps, nested resource paths, wrong-instance, ambiguous-pairing, and
fresh-field tests keep their semantics. Equivalent direct/callback applications
use the same internal map rules. Expansion spells the existing user binders
and introduces no kernel identities. Test binder work across multiple sizes.

### W7 — Qualify the combined abstraction and remove obsolete paths

**Dependencies:** W1-W6 integrated green. **Owner scope:** final compatibility
review, bounded end-to-end tests, cleanup of obsolete adapters, documentation,
and issue reconciliation. Not a catch-all for new language features.

Tasks:

- Run the complete R1-R6 matrix on the integrated branch. Use explicit simple
  proofs where practical so success does not depend on new search heuristics.
  Keep each regression small; do not build one giant callback expansion test.
- Exercise raw/wrapped memory, tokens, folded composites, and exclusive
  instances through direct calls, callback calls, explicit refinement, and
  existing automatic formation where supported. Preserve negative cases.
- After ordinary verification succeeds, run representative expansion followed
  by verification and the relevant audit/profile consistency checks. Use the
  shared bounded verification engine, not recursive CLI/test subprocesses.
- Review for duplicate evaluators, independent effect derivations, special-case
  callback retention, obsolete binder registries, and whole-context scans.
  List necessary memory-family specialization separately from deleted duplication.
- Update `docs/concepts/resources.md`, `docs/concepts/contracts.md`,
  `docs/internals/architecture.md`, and affected internals/reference text to
  explain the shared model and retained semantic distinctions. Do not document
  excluded extensions as implemented.
- Reconcile the completed G1-G3 and binder cleanups in `function-contracts.md`;
  retain unrelated G4-G7 work. Do not delete that issue unless all of its own
  remaining acceptance criteria are actually met. Do not create new issues
  for discoveries without explicit user authorization.

**Done:** all criteria below are met on one integrated commit. Delete this
issue and its index entry only when the implementation, regressions, and
documentation have landed.

## Gate and worker handoff requirements

Every implementation chunk must run relevant focused tests and an unfiltered
`scripts/check.sh` in its task worktree before integration. Judge the gate by
its exit status, not piped output or `cargo test --lib`. Follow
[testing.md](../docs/internals/testing.md) and
[verification-efficiency.md](../docs/internals/verification-efficiency.md).
Changing a performance-sensitive representation requires deterministic curves
over at least four sizes in the same chunk, not deferred until W7. This plan
does not claim a measured current scaling defect; the curves protect the
refactoring's required complexity.

Each handoff must state:

1. Chunk ID, starting commit, resulting commit, and files/interfaces changed.
2. Behavioral tests added/updated, including negative cases and R IDs covered.
3. Exact focused/full-gate commands and exit statuses; scaling counter names,
   input sizes, and observed work where applicable.
4. Which old path was removed, or the adapter's named removal owner.
5. Remaining blockers and whether they are verified failures or hypotheses.
6. Confirmation that no language semantics, C source, budgets, quarantine, or
   unrelated files changed to obtain success.

Before integration, verify the primary checkout is clean and its base matches
the tested predecessor; rebase/update and rerun affected gates if it moved.
After an interrupted or timed-out verifier, confirm its process tree exited.
Report unrelated tooling blockers rather than accepting a slow eventual pass.

## Overall acceptance criteria

- Existing syntax and the language-preservation contract above are intact.
- R1-R6 are checked by bounded positive and negative regressions; documented
  callback workarounds are removed only where the real behavior now verifies.
- One normalized resource specification and shared contract interface serve
  direct functions and callbacks, with distinct checked evidence where needed.
- Contract clause evaluation does not lose available authority simply because
  an address depends on memory inside a folded resource.
- Resource transitions supply the authoritative checked memory effect
  projection; no duplicated evaluator or footprint reconstruction remains as
  an alternative source of truth.
- Observations survive precisely when their support permits it, scoped views
  do not escape, and callback facts remain tied to the correct pointer value.
- Existing binder forms share internal identity/substitution rules while
  preserving return snapshots, exclusive identity, and fresh fields.
- Required deterministic scaling, ordinary verification, expansion/reverification,
  certification, and relevant audit checks pass without weakened gates.
- `scripts/check.sh` passes on the final integrated implementation, documentation
  is current, and overlapping issue statuses accurately reflect completed work.
