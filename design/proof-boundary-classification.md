# Proof boundary classification

Source reconciliation at `c53645952` (2026-11-11), the completed head of
PR #2520. Queue/merge status is separate from this source baseline. This
classifies all 16 `mixed` records in `build_support/proof_search_edges.tsv`
and groups the 6 operation references. The operation-to-driver list is empty.
A record is one caller/target pair, not one runtime call or one slow walk.
A classified call is not a complexity proof for its callee. This documentation
pass adds no measurements; preparation evidence below is from the completed
implementation's tests. The subsequent diagnostic cleanup removes one
operation-to-driver record: an exhausted callback script now reports its actual
frontier without speculative execution or solving. Match-arm contradiction
dispatch now lives in the match driver: preparation returns the excluded
partition, the driver applies the written contradiction with its source site,
and completion publishes the retained partition and closed-arm certificate.
The relocated match reference is driver-owned. Signed-definedness certificate
attempts and unsigned strict-fact restatement now live on `ProofSearch`;
primitive certificate application is unchanged. Registering these helpers exposes
existing search-only callers without adding runtime work. Invariant-bundle
closure, its scope wrapper and member solve dispatch now live on the driver;
selected-obligation diagnostics and explicit Both/Intro certificates are preserved.
Resource-opening candidate selection now lives on `ProofSearch`; explicit
unfold and statement operations are unchanged. Live-state transport premise
planning and returned-state transport planning are also on `ProofSearch`.

## Current boundary

`Proof::begin_have` and `Proof::begin_contract_claim` return prerequisites;
`ProofDriver::open_have` and `ProofDriver::open_contract_claim` schedule their
proofs. These are no longer outstanding operation-to-driver records.
`ProofScope::join` and its resource-close operation now report outstanding
body facts through the same obligation channel. `ProofDriver::complete_scope`
schedules their written or implicit proofs; nested resource scopes use
`complete_nested_scope`. Creating an obligation is allowed fast work; choosing
an omitted proof's ordinary solve is legitimate driver work. The remaining separation-observation setup cost is a
separate question from who solves its obligations.

The driver now interprets C-branch and proof-case arm scripts. The proof object
retains split, arm focus, checked entry and join operations; it does not invoke
arm-script callbacks. Resource scopes incorporate the driver's direct checked
branch successor through `with_completed_execution_if`. This preserves their
parent-identity checks and retained history. It does not establish a complexity
bound for every existing split/join helper.

Step/fold preparation now retains a conditional successor and obligations.
`ProofDriver::apply_bare_statement_step` and `apply_execution_statement_step`
prove them at the original input; `Proof::finish_prepared_step` publishes the
retained result without re-executing the primitive. Failed preparation is a
final refusal. Named, population/authority, operational wrapper, completed-return
and legacy definition-law folds use this boundary. Return folds retain path
endpoints; legacy folds no longer test whole-path certification to select a
fallback exchange. These are closed preparation tasks, not outstanding adapters.

Scoped evidence: twelve named preparation controls passed on this baseline,
including constructor counts at 1/8/32, missing-premise refusals, and expansion
and cold replay. MemoryState-pointer and arithmetic-field regressions preserve the
meaning of generated obligations. This establishes the selected routes, not a
cost bound for every evaluator, observation, join or contract-closing operation.

Two separate limits remain:

- Arithmetic evaluation still decides some safety conditions before emitting
  obligations. Driver-owned solving does not make that generation work fast.
- `ProofDriver::with_proved_lowering_requirements` still probes and invokes its
  operation again after proving lowering requirements. Its callers include
  have/claim opening and explicit unfolds. This is not the removed step/fold retry
  and not hidden solving inside `begin_have`/`begin_contract_claim`. Establish
  a complete-operation cost violation before treating bounded repeated lowering
  as a bad-scaling defect.

## Statement-exit fact transport: removed operation discovery

Statement publication retains producer facts at their original states.
It no longer calls condition transport to discover bonus final-state facts,
builds no extra transport context, and adds no replacement obligations.
Existing producer-issued transport metadata is still published.

A test-build `FastOperationScope` guards result publication; condition fact
transport is registered as discovery even though the helper does not construct
`ProofSearch`. The adversarial guard test rejects that crossing, and an ordinary
call-assignment proof checks that the result and postcondition remain available.
This closes this call site, not every search reachable during step preparation.
See [remaining coverage](../docs/internals/verification-efficiency.md#operation-audit-ledger).

## Findings

The old categories describe code placement, not the reason search runs. Most
ambiguous references are expected orchestration or discovery helpers. Two
other concerns need separate treatment: remaining orchestration adapters on
operations and declaration validation that searches outside proof scripts.

The known direct operation/search dependencies remain: this classification does
not eliminate the four kernel bridges, their 17 caller records, or the 6
Surface operation/search records. In particular, explicit premises are not an
explicit derivation: `transport(...) using {...}` is classified Simple in
`src/surface.rs`, but its application can still call `derive_atomic_proposition`.
Bare `transport(...)`, by contrast, is classified Smart and may discover evidence.
Expanding the latter into the former is not by itself a search-free guarantee.
`preserve(...)` is a different operation and must be audited separately.

## The 16 mixed reference records

Paths below are relative to `src/surface/`.

| Caller | Records | Classification and source evidence |
| --- | ---: | --- |
| `check_initialization_body` | 2 | Driver dispatch. In `proof/execution_planning/loop_planning.rs`, omitted/written solve calls the solver; a written script calls the script interpreter. |
| `verify_loop_initialization_pure_proof` | 1 | Driver dispatch. Executes explicit phase-helper unfolds and `have` bodies. |
| `verify_one_loop_preservation_proof` | 2 | Driver dispatch. Invariant search is under `region_solve.is_some()`; retained bodies take a different route. Also prepares invariant obligations through the driver. The surrounding state-join/revalidation work still needs its own cost audit. |
| `check_direct_pure_goal_with_proof` | 2 | Driver dispatch. Discharges entry obligations, then runs ordinary solve for an omitted or written solver proof. |
| `check_pure_script_with_proof` | 1 | Driver dispatch. Runs written proof steps and discharges outstanding entry obligations. |
| `verify_contract_refinement_theorem` | 1 | Driver dispatch. Executes the refinement proof script. |
| `verify_theorem_ensure` | 1 | Driver dispatch. The inventoried calls discharge declaration-entry obligations, including trusted-theorem declaration paths. |
| `try_steps` | 1 | Search support. `proof/attempt.rs` tries candidate steps under an attempt budget; production callers are in `smart_closures/search.rs`. |
| `plan_explicit_loadability_transport` | 1 | Search support. `surface_certificates.rs` selects/minimizes premises and returns written tactics for solve. Here “explicit” describes the output, not the planner's cost. |
| `plan_explicit_predecessor_upper_bound` | 1 | Search support. Used by solve directly and by the recorded signed-order planner; may plan equality rewrites. |
| `plan_explicit_fact_transport` | 1 | Smart transport planner. Reached from smart execution and the bare-transport adapters on `Proof`; builds contexts from available facts/effects and tests derivability. Ordinary expansion covers the scalar routes listed in T1–T5; surviving legacy output still uses `TransportUsing`, whose remaining search is not excused by this classification. |
| `segment_contains_pointer` | 1 | Declaration-validation search. `checking/segments.rs` calls `ProofSearch::proves` for bounds; the production caller is resource-definition read-coverage validation in `validation/definition_validation.rs`. This is not ordinary implicit solve on a user proof obligation. Determine the declaration-input cost bound and how expensive reasoning can be replaced by explicit evidence. |

Totals: 11 interpreter/obligation-dispatch records, 4 discovery/support records
(including bare transport), and 1 declaration-validation record.
These roles should eventually replace the ambiguous labels after review; this
audit deliberately does not silently regenerate the enforced inventory.

## Operation-to-driver adapters

No operation-to-driver reference records remain in the frozen inventory.
Invariant closure belongs to `ProofDriver`; arithmetic attempts, resource opening,
and live/returned transport planning belong to `ProofSearch`. Their existing
algorithms, generated steps and refusals are unchanged. This ownership split
makes the calls explicit; it does not establish the cost of their callees.

## Why accidental search remains possible

1. `kernel::search::ProofSearch<P>` is a namespace with static associated
   functions. `proves(context, goal)` needs no search-access argument. Merely
   moving a method here does not make it unavailable to operations.
2. Every Surface `Proof` and `ProofScope` implements `DriveProof`; `.driver()`
   can be obtained inside operation implementations. This leaves an interface through which an operation could acquire the driver;
   the frozen inventory now rejects new such calls, but a scoped capability
   boundary would make the separation stronger.
3. `without_implicit_solve` gates automatic solving at selected sites. It does
   not prohibit direct `ProofSearch` calls or legacy search wrappers. Passing
   cold replay under it is useful evidence, not the full no-search condition.
4. `SearchPermission` protects selected ambient enumeration interfaces. It
   is not required by every search entry point or every potentially growing
   collection operation. Its current scope is narrower than the desired rule.
5. The build inventory recognizes registered names, method references and macro
   tokens. It is lexical, not a transitive/type-resolved call graph. Driver
   classification is largely by placement, so code added inside a driver can
   be inventoried without proving that it is legitimate search dispatch.
6. Work can be bad without calling any search API: rebuilding contexts, copying
   terms, validating a result already constructed, traversing history, and
   enumerating growing index buckets. Source guards alone cannot detect this.
7. Setup and error reporting need their own cost contracts. Moving expensive
   work before the first step or after failure does not establish the overall
   fast-proof guarantee, and there may be no tactic the user can expand there.

## Recommended next boundary, for design review

Keep the existing persistent proof state and direct successor construction.
No second checker or producer/rechecker layer is needed.

- Primitive operations return a successor or outstanding obligations. They
  cannot acquire a driver or invoke a proof script. The outer driver executes
  supplied proofs, invokes solve when omitted, and publishes the retained result.
  Have/claim opening and resource-scope completion delegate solving; step/fold
  completion also retains its prepared result without re-execution;
  move the identified script/search adapters out of the primitive interface.
- Make search access explicit at every discovery entry, including compatibility
  wrappers: a driver-owned access capability passed to search, never stored in
  the proof state or handed to primitive operations. Restrict its construction
  to reviewed smart/implicit dispatch, not arbitrary driver methods. The
  existing partial `SearchPermission` mechanism is a starting point, not
  evidence this is already enforced.
- Add a strict replay/operation guard against **all** registered discovery,
  not just implicit solve. During migration, name existing exceptions and make
  new ones fail. A primitive invoked by a search still runs under the fast
  restriction; being inside solve must not exempt its internal work. The guard
  checks access policy at execution time; it does not replay or revalidate a
  proof result.
- Keep deterministic complete-operation scaling tests for the work no search
  boundary can detect. Fix explicit input/state delta, grow unrelated state,
  and cover successful, failing, cold, repeated and persistent-branch cases.
- Give normal diagnostic work a bounded interface over retained error evidence.
  Treat further speculative execution as an explicitly requested diagnostic
  search rather than work silently performed to report a fast failure.

Have/claim opening and resource-scope completion no longer schedule proofs
from the primitive interface. Branch script interpretation now also lives in the driver, including the
proof-level `if` path that formerly ran script callbacks inside a primitive.
The inventoried adapters above are extracted. Definition-validation proof support
needs separate design review. Callback failure reporting now uses the actual
frontier; it performs no speculative continuation.

## Reconciled operation dependencies

The 6 `operation` records are not 6 independent slow walks:

| Group | Records | Current interpretation and remaining evidence |
| --- | ---: | --- |
| Theorem application on `ProofDriver` | 1 | Pure, fixed-state, live and returned-outcome named applications retain arguments and conclusions while the driver solves their obligations. Population-member-count-zero and Integer range-fold built-ins use that same obligation route. The selector edge remains for unsupported outcome dispatch. Migrated primitives have test-build discovery guards; generic applications instantiate checked statements without re-running declaration proofs. The guard does not certify unregistered helper loops as fast. ArithmeticUsing remains smart and dispatches through search. |
| Legacy explicit transport checking | 3 | `certified_fact_transport_reaches`, `check_fixed_state_fact_transport_using_facts_inner`, and `apply_pure_transport_using` call atomic derivation. Confirmed search access from the explicit transport route; migrate/retire under T1–T5, not a new independent bug per record. |
| Definition validation | 2 | `symbolic_segment_covers_index` and `symbolic_segment_covers_range` join the mixed `segment_contains_pointer` record in one declaration-validation concern. There is no ordinary user obligation/expansion boundary established for these checks. |

At this audit baseline, four kernel bridges mapped to three groups: loan
aliases and access (L1), ownership candidates (R2), and call framing (C1). The
[operation ledger](../docs/internals/verification-efficiency.md#operation-audit-ledger) tracks the active work.

## Evidence and ownership

- **Confirmed boundary problems:** legacy simple transport can access search.
  This is a source-established architectural finding, not a newly measured scaling curve.
- **Known cost violation:** T5 reconstructs transition assumptions using
  `assume_proposition_uncharged`. Ordinary transport expansions cover selected
  cases but do not make the surviving legacy route bounded.
- **Legitimate expandable work:** omitted-obligation solve, explicit smart
  tactics, and discovery planners. Their generated operations still owe the
  fast-checking guarantee; being called from search grants no exemption.
- **Unmeasured/coverage work:** the three bridge groups, transition checks, declaration validation, and operation-map growth axes.
  An unresolved label is an investigation task, not proof of a bug.
- **Owned elsewhere:** `roadmap/kernel-term-split.md` owns the remaining
  shared-term representation boundaries. Its original R1–R7 reproductions are
  closed; use its current closure checklist rather than reopening those groups.
  Representation costs can occur without any `ProofSearch` call; do not duplicate
  their fixes here.
  Memory-history coverage M1 belongs with the program-point memory migration in `roadmap/smart-tactics.md`;
  scaling lifecycle E1 and quantifier Q1 retain their existing deferred owners.

The inventory contains 662 reference records, not 662 obligations to remove.
The classified mixed records are no longer an unknown pile. What remains
unknown is complete-operation cost on the named routes, and whether the
unreviewed parts of the verifier contain additional routes. Consequently this
reconciliation supplies a finite investigation list, not a global bug count or
a claim that expanded proofs cannot create `ProofSearch`.

## Operation discovery guards and reproduced crossings

Test-build discovery guards enforce `ProofScope::join`,
`Proof::finish_prepared_step`, `Proof::begin_have`, `Proof::begin_contract_claim`, and kernel
`ProofObject::focus_contract_claim`, in addition to the three theorem-application
primitives. Driver obligation solving runs outside those operations. Source
mutation tests prevent deleting or postponing their guards. The guards detect
registered search, not uninstrumented loops or copying.

The same guard cannot yet be retained on `prepare_step`.
Earlier whole-operation probes reproduced these operation/entry pairs:

| Operation | Discovery entry | Reproduction (`mdtests/`) |
| --- | --- | --- |
| `prepare_step` | `loan_access` | `a_32_bit_cell_read_at_the_other_signedness_is_its_sign_cast.md` |
| `prepare_step` | `ownership_validity_candidates` | `a_callee_owns_a_window_of_a_64_bit_range.md` |

These reuse two existing bridge entries; they are not two new independent
walks. A first guard failure can mask a later dependency. No guard escape was
added, and the existing source dependency records remain frozen.

Removing optional call-partition inference exposed `call_frame` through
`call_kept_ownership` in the same 64-bit window fixture. With instance-body
opening removed, frames without owned composites now construct their kept set
directly; that route no longer enters `ProofSearch::call_frame`. Composite
families still do. Re-probe complete preparation before treating the old
window's first-failure entry as current. At the audit baseline, the local
signedness fixture reached `loan_access` through
`memory_write_permission_outcome_for_local`. The temporary probe was removed.

Call entry-borrow restoration has a separate discovery guard. It restores
retained entry identities to their residual frame without validating that
partition again. Only call application with entry-state borrowed outputs creates
the private transfer carrier. New produced ownership, post-state outputs,
body-return descriptions and contract comparisons retain validation. This scoped
guard does not cover their raw resource construction or complete `prepare_step`.

Selected ownership overlap has its own discovery guard. It compares the
supplied ranges and recorded base/endpoint equalities; it does not enumerate
alias spellings. Ownership candidate selection remains a separate bridge.

Have opening no longer reconstructs a composition-only context. Other selected
observation routes can still derive separation before the written proof runs.
`single_write_resource_transport_expands_to_preserve_without_search`
is a focused positive reproduction. Claim opening retains its goal and reports
missing evaluation prerequisites; it does not materialize the separation being
claimed. The explicit proof can use the exact partition rule in `close()`
or ordinary separation laws. Driver-owned implicit solve remains outside the
operation guard.

The loan-access crossing above is historical. Local assignments and the
remaining write routes have migrated to retained loan evidence. The legacy
guard now has only test callers. Re-probe complete preparation for other
crossings before adding a whole-operation guard.

These guards establish absence of registered discovery on their exercised
routes, not fresh complete-operation scaling curves or a global fast-proof
guarantee. Have opening and statement preparation remain separate work.

Pointer decisions no longer discover separation from owned compositions or
pointer alias components. An explicit separation fact supplies the indexed
disequality consequence. The complete-query alias scaling control and source
partition proof cover this route; other condition-decision walks need their
own evidence.
