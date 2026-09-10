# Remove search, fuel, and fallbacks from the kernel

## Violated invariant

The kernel checks; it does not search. An authoritative kernel operation may
apply a fixed collection of exact rules, traverse the explicit input or
certificate it was given, and use indexed lookups into ambient state. Its work
and completeness must not depend on an opaque fuel, recursion-depth, or retry
limit, and it must not fall from a local check into speculative or global proof
search. Search belongs to the surface's smart tactics, whose successful result
is a sequence of checked operations or another explicit certificate.

"No fallback" means no broader **search** fallback. It does not prohibit a
short, deterministic sequence of sound rules that each answer from their named
inputs. For example, syntactic equality followed by an indexed lookup is one
exact decision procedure, not forbidden search. The boundary is crossed when
failure starts candidate selection over unrelated ambient facts, recursive
proof attempts, or alternate global reconstructions whose cost is not charged
to explicit input or output.

The working rule is:

- A walk over a term, a memory DAG, an equality class, a fact's disjuncts, or
  another explicit structure is bounded by that structure. Use an in-progress
  query set where it can revisit a node, and an iterative implementation where
  Rust stack depth is the concern. Do not make logical completeness depend on a
  numeric depth cut.
- Enumeration is allowed when the operation or certificate explicitly names
  the enumerated input and the deterministic work is charged per item. A
  surface tactic may choose that input; the kernel checks exactly what it is
  given.
- Branching whose candidates come from the ambient fact set is planning. Move
  it to a surface smart tactic and retain enough evidence for the kernel to
  check the selected route without rediscovering it.
- Fixed memo capacities may evict cached results but must not change an answer.
  Execution path, loop-unroll, and call-depth budgets are semantic execution
  capacity and are not proof-search bounds; they remain independently owned.
- A wall-clock deadline is crash containment, not a negative logical answer.
  Expiry must propagate as a verification-limit error, must not be cached as
  `false` or `None`, and must not make a later result depend on when the clock
  happened to fire.

A search that constructs a derivation and checks it inside `src/kernel/` is
still authoritative kernel search if the result issues a theorem, discharges
an obligation, or advances a proof object. Checking the discovered derivation
afterward establishes soundness, but it does not establish the intended
search/checking boundary.

## Status

Many dead routes, environment switches, duplicate evaluators, artifact-less
execution paths, fallback ladders, and old fuel counters have been removed.
Several well-founded walks now use exact in-progress query guards;
`ResolutionQueryGuard` in `src/kernel/reasoning/memory_resolution.rs` is the
pattern. Enumerations over explicit quantifier instances, disjuncts, and fold
steps are charged as deterministic work per instance. Deterministic work over
the profiled examples fell or held during that cleanup.

The structural, canonicalization, finite-splitting, and load-equality
migrations described below are complete, as is the incomplete-answer audit.
The authoritative-caller audit is recorded below; migrating its remaining
searching authority boundaries is still open.

The load-equality migration replaced every successful global-fallback use
with consumer-owned evidence. Fixed-state restricted `simp` retains a
snapshot-anchored `transport`; resource rewrites and observations retain the
checked equality they consume; contract materialization retains typed
witnesses on the function-claim proof object; and indexed stores and pointer
ranges retain exact separation and signed-order paths. The checked-call event
slice and the direct framed-transport migration are complete.

Tagged-pointer `recorded_uint64_equals` now uses only its observed
assumption-free direct snapshot match, and the unused global framed-load
prover and its memos are deleted. The 30 successful dependent roots found by
the residual census now retain a finite witness: the two load origins, pointer
offset congruence, and either a direct snapshot match, a typed memory-DAG path,
or an exact effect-summary fact with per-range disjointness evidence. Broad
fact matching checks this retained evidence and at most one resolved endpoint;
it no longer launches arbitrary term-pair recursion.

Consequently `MEMORY_LOAD_EQUALITY_DEPTH_LIMIT` and its truncation accounting
are deleted without a replacement tier. The regression suite covers retained
singleton-bound evidence, memory-DAG paths of increasing length, indexed
separation in the presence of unrelated facts, and independent rechecking of
the expanded old-load proof. On owned-vector, the slowest simple check fell
from 9,230 to 3,855 deterministic work units and the previous 10,079-unit
load-equality-dependent smart hotspot disappeared; total profile time fell
from about 5.70s to 5.31s. Perpetual-service's measured simple work remained
essentially flat (1,731 to 1,678 units for its slowest check).

The first two ordered changes are complete. This issue now states the
operational boundary and corrected inventory, and the unused general pointer
distinctness fallback has been deleted. Click has no compatibility commitment
for the low-level kernel API, so its contextual theorem constructor was deleted
with it rather than deprecated or replaced with a compatibility shim. Memory
resolution retains only its narrower exact, query-bounded distinctness check.

Structural cleanup owned by this issue is complete. Exact-load materialization
and normalization follow complete acyclic chains with exact cycle detection,
using iterative term reconstruction where nesting can be deep. Call-havoc
write-set markers now use a complete iterative, length-delimited structural
encoding;
two write sets that first differ below the former depth limit produce distinct
memory endpoints. Nested quantified candidate comparison now lives with its
surface theorem-application caller: its indexed logical fragment uses the
complete alpha-invariant key, and unindexed proposition shapes use an exact
unbounded quantifier walk. The indexed walk has a multi-size deterministic-work
regression, and the unindexed fallback has a regression beyond the former
depth limit.

Upper-bound splitting now also lives in the surface smart closer. It selects a
recorded bound and emits an ordinary checked proof `if`, with explicit theorem
applications deriving the terminal equality arm. The kernel split rule, its
whole-context derivation payload, and `UPPER_BOUND_SPLIT_DEPTH_LIMIT` are
deleted. The two bound-universal bubble fixtures verify both the smart proof
and its independently parsed expansion, including the emitted branch.

The resource-invariant theorem constructors no longer call the general
proposition prover. They now issue authority only for an exact recorded
context fact, retained as the explicit identity implication `fact -> fact`.
Derived count and nonnegativity facts must therefore be planned and recorded
by the surface before theorem construction; a regression rejects a merely
transitive contextual consequence. This completes the
`theorem_from_contextual_proof` part of the authoritative-caller audit.

The arithmetic interval depth was removed from this structural-cleanup queue
after reviewing the abstraction around it. `arithmetic()` is a nominally simple
tactic whose kernel operation reconstructs an affine and interval derivation
from the named premises. The intended fix is to make it a surface smart tactic
with explicit checked evidence, not to make that hidden kernel decision
procedure iterative. That migration, including `ARITHMETIC_INTERVAL_DEPTH`, is
tracked in `issues/arithmetic.md` and is deliberately deferred here.

The three canonicalization-related cuts were also found to share a deeper
abstraction problem. The completed canonicalization migration separates
assumption-free, idempotent `canonical_term` from contextual proof vocabulary:
verified calls retain canonical footprints, exact `frame using` operations
carry proof-local endpoint evidence, and target-directed load-address
congruence replaces the former implicit representative walk. The alternating
round limit and the deep-term canonicalization preflight are gone. The final
theory-aware order-endpoint cutoff is now gone too: complete input-sized key
and residue walks preserve indexed candidate selection without introducing an
unbounded search.

## Current inventory

Loop back-edge migration is complete (2026-09-09). Bare `close_invariants()`
and automatic preservation now plan retained `close_invariants by { ... }`
proof bodies. Explicit bodies prove the exact lowered value and safety goals;
closure validates their context-bound evidence without rediscovery. The legacy
path builder, prefix probe, and alternate lowering-record producer are deleted.
The remaining fixtures use existing explicit tactics without changing their C
or invariant statements. Initialization rechecking preserves the original
lowered goal and its binders.

Older counts retain their stated measurement dates. The reentrancy census was
rerun on 2026-09-07 at `2e14f553` over the then-complete corpus: 25 example
projects, 817 mdtests, and 1,631 unit tests.

### Structural and fixed-point cuts

These are not surface-search migrations. Replace each cut with work bounded by
the complete named structure, plus an exact cycle check or an iterative walk as
needed.

Removal of the order-endpoint key depth is complete, along with its former
sibling cuts: the alternating contextual-lowering rounds and deep-term
canonicalization preflight.

There are no remaining structural or fixed-point cuts owned directly by this
issue. Nested quantified-binder comparison is complete and lives in the
surface generation path. The canonicalization family is complete; arithmetic
interval work remains separately owned as described above.

`ATOMIC_PREMISE_MINIMIZATION_DEPTH` (`src/kernel/assumptions.rs`) and
`VERIFICATION_SESSION_DEPTH` (`src/kernel/mod.rs`) are nesting-state flags, not
logical cuts. Cache-size constants are eviction policy, not completeness
bounds. Neither category is part of the list above unless it is later shown to
change an answer.

### Search and tiering

Finite context splitting is complete. A 2026-09-07 census found no successful
use in the examples and 156 successful mdtest invocations: 134 singleton
ranges, 18 two-value ranges, and 4 three-value ranges. Disabling the rule
changed only 5 of 789 mdtests. An exact singleton rule recovered four; the
only genuine multi-value dependency was `local_array_loop_frame`, where direct
symbolic element-index extraction had failed to feed the existing array-bound
checks. Fixing that structural path recovered the last fixture without a case
split. None of the observed two-value splits was necessary.

`FiniteContextSplit` and `FINITE_CONTEXT_SPLIT_LIMIT` are therefore deleted,
with no general surface case planner. The retained `SingletonSubstitution`
proof-object node is not a split: it names exactly the two indexed order facts
that force `x == constant` and the proof of the substituted proposition. It
does not retain, clone, or scan the ambient context.

The former `bounded_snapshot_comparison_active`, `ENDPOINT_BRIDGE_ACTIVE`, and
`DERIVATION_WALK_ACTIVE` tiers are already deleted. The remaining names have
these dispositions:

- `LOAD_EQUALITY_RESOLUTION_ACTIVE` guarded 1 example, 293 mdtest, and 29 unit
  attempts. The guarded route proved zero queries and suppressed zero nested
  calls in every corpus. It was a dead fallback, not a replacement-evidence
  problem; the route and flag are deleted.
- `ALIAS_GUARD_REFUTATION_ACTIVE` guarded 718 example, 4,063 mdtest, and 6,676
  unit attempts. The rule proved zero fixture queries and exactly one unit
  regression; the broad flag suppressed zero nested calls. The narrow
  alias-refutation rule remains, but the unused boolean tier is deleted. Its
  range checks use only the bounded shallow fact graph; any demonstrated cycle
  belongs in an exact-query guard rather than a rule-wide switch.
- `inside_condition_decision` was observed 14,417 times in examples and 21,339
  times in mdtests, but it does not reject a nested decision. It only prevents
  a nested fact set from installing a new ambient memo-id scope; the exact
  `ConditionDecisionGuard` still admits distinct nested conditions and rejects
  only a repeated condition. This is memo-scope policy, not a coarse
  incompleteness tier, and is removed from that inventory.

### Incomplete-answer and authority audit

1. **Complete: `incomplete_reasoning_epoch` and negative-memo gating**.
   The renamed epoch records exact condition-, simp-fact-, memory-resolution-,
   and resource-composition cycles, plus every observed kernel verification
   limit. It is monotonic thread-local invalidation state, not a work budget.
   Decision, constant-normalization, atomic-derivation, transport-equality,
   context-inconsistency, and resolution memos compare epochs around queries.
   Positive evidence remains reusable. Delete the mechanism only when
   incomplete nested answers cannot reach a memo boundary.
2. **Complete: kernel deadline checkpoint audit (2026-09-07)**. All 31 former
   raw checkpoint sites now route through `reasoning_interrupted`, which calls
   instrumentation exactly once and advances the epoch on interruption. This
   preserves deterministic checkpoint costs and covers tactic work exhaustion
   as well as wall-clock limits. The audited families are:

   - Execution budgets (2): return `ExecutionLimit::Deadline` directly.
   - Assumption reasoning (11, including the simp wrapper): proposition and
     region checks, order traversal/collection, and inconsistency caching.
     Interrupted order collections remain uncached.
   - Memory resolution (1 wrapper): protects enclosing negative query memos.
   - Memory provenance (10): frame transport and effect equality return misses;
     exact-load normalization retains an unnormalized remainder on expiry.
     Both now invalidate enclosing negative answers.
   - Contract certification (7): loadability witnesses return conservative
     misses, now recorded as incomplete.

   Internal boolean/optional helpers retain their existing signatures. At the
   verification boundary, execution limits, `check_verification_deadline`, and
   `ClickError::new` report the limit context before an ordinary semantic miss
   can escape. Existing regressions cover wall-clock and work-budget error
   precedence; a resolution-memo regression expires a nested proposition check,
   exits the deadline scope, and confirms the same query can subsequently prove
   and cache its positive answer. This audit covers the existing checkpoint
   sites, not the responsiveness of every checkpoint-free structural walk.
3. **Audit complete; migration open: general-prover authority**. The static
   audit below finds more than loop and effect certification: proof-object
   event checks, quantified fact availability, pure-theorem construction,
   contract execution/refinement, and termination also retain general reasoning.
   The former `theorem_from_contextual_proof` resource constructors remain
   complete (exact recorded facts only); that does not make all resource-event
   validation search-free. Do not narrow the issue's invariant merely to close
   it, or treat a ban on direct `PureFactContext::proves` calls as a transitive
   authority check.

### General-prover authority inventory (2026-09-07)

Audited at `8cdf0b69`. This is a static caller/consumer audit, not a dynamic
success census. It inventories `proves`, `derive_proposition`,
`derive_proposition_without_premise_minimization`, and `derive_simp_proposition`
outside their recursive implementation, follows wrappers to consumers, and
separates test-only and metadata callers. It does not certify every lower-level
`decide`, atomic-theory, resource-matching, or derivation-checking helper as
search-free. Those helpers still need review when their consumer is migrated.

`PureFactContext::proves` is not an exact membership test: after direct rules
it can try context inconsistency and singleton substitution; logical goals
also recurse through alternatives and extended contexts. The derivation
builders explicitly search for proof trees. A positive result may be sound
while still violating the search/checking boundary.

| Consumer / source anchor | Authority currently decided by general reasoning | Disposition |
| --- | --- | --- |
| Proof-object events: `proof/execution.rs` resource rewrite/observation `check` | Pure resource deltas now use exact availability or retained local proofs. Branch-interface judgments retain completed local proofs, including load-definition and exported-resource read evidence. General fallbacks for theorem premises, common successor facts, and split obligations are also removed. | Complete for these pure-delta fallbacks; broader resource matching/ownership and definition instantiation still need their own migration. |
| Fact availability: `proof/facts.rs::matching_quantified_facts` and `proof/fact_reasoning.rs::quantified_equivalent_available_fact` | After binder equivalence fails, tries simp in both directions for a candidate quantified fact. Reached by pure `assumption` and cross-effect availability, not only smart planning. Indexed candidate selection does not remove this recursive proof attempt. | Keep exact/binder matching; surface should select and prove a nontrivial conversion explicitly. |
| Context-free closure: `proof/fact_reasoning.rs::normalizes_context_free`, used by `proof/object.rs::apply_normalize` and quantified guard/instance checks | Tries atomic derivation, then general derivation, even though the ambient context is empty. | Distinguish input-bounded definitional normalization from logical proof construction. Keep the former; expose explicit logical steps for the latter. Empty context alone is not a search-free guarantee. |
| Pure-theorem authority: `api.rs::prove_universally_quantified_pure_implication` and its `_by_int32_rewrites` variant | General constructor proves the conclusion from requirements. Rewrite constructor names an ordered rewrite list but still proves each equality from requirements and calls the general boolean prover for final context-free closure. Both have surface consumers in `proof/pure_theorems.rs`. | Accept the already constructed proof and checked rewrite premises; an explicit rewrite order is only part of the required evidence. |
| Calls, refinement, and resources: `functions.rs`, `primitives/resource_algebra.rs`, `primitives/contracts.rs::applicable_verified_loop_rule` | Proves guarded requirements, footprint guards, refinement obligations/conclusions, quantity relations, population transitions, resource facts, and loop-rule prerequisites. Results affect accepted calls, resources, or selected rules. | Split by consumer; retain guard, quantity, and refinement evidence. Do not replace every call with an exact lookup in one large completeness-breaking change. |
| Lowering/execution: `spec.rs`, `reasoning/path_facts.rs`, and remaining `loops.rs` helpers | Decides spec branches, overflow obligations, invariant paths, segment containment, and whether an obligation or fact can be omitted. Some paths have explicit no-search modes, but they are not universal. | Propagate unresolved obligations and retain branch/containment evidence. Separate proof-relevant discharge from redundant-fact suppression. |
| Termination: `termination.rs::assume_structural_path`, `ranking_proves`, `ranking_proves_lexicographic_decrease` | Discharges structural-path obligations and ranking conditions before `c_verified_function_termination_rules` issues authority. `ranking_proves` also collects ambient condition facts for an arithmetic fallback; lexicographic checking tries pivots. | Keep the named ranking expression/tuple as input, but move proof and pivot selection to planning and retain their evidence. |
| Legacy public theorem constructors: `api.rs::prove_c_function_satisfies_specification_and_propositions`, `prove_c_statement_executes_and_propositions` | Proves arbitrary added propositions and issues a theorem. No non-test in-repository caller was found. | Candidate deletions after checking all exports/callers; public but unused is not the same as test-fenced. |

Additional distinctions that matter for the migration:

- `assumptions.rs::record_reasoning_provenance` constructs a general derivation
  only while collecting planning metadata. The returned premises are not
  theorem authority. Moving this helper is organizational work, not an
  independent soundness boundary repair.
- `proof/fact_reasoning.rs::fact_conflicts_with_assumptions` has surface
  consumers, rather than a direct kernel proof-object consumer in this audit.
  Inspect the selected transition's retained evidence before classifying an
  individual surface use; a helper's directory alone is not the boundary.
- `ProofFacts::with_selected_resource_separation` also has surface callers,
  but returns augmented facts rather than inert planning metadata. It needs
  consumer/evidence review; it cannot be waived merely because its caller is
  surface code.
- `assumptions/memory_reasoning.rs::pointer_access_in_range` calls `proves`
  internally for bounds. It is part of the reasoning engine, not another root;
  a replacement loadability checker must not inadvertently retain that route.
- `api.rs::prove_c_while_invariant_rule` and the new deadline-memo regression
  are test-only. They are not production migrations. Likewise, occurrences in
  source-ban strings are not calls.
- Atomic derivation entry points were inspected separately: explicit guard
  checks and single-premise loadability checks use them too. This audit does
  not equate every atomic check with global search, nor certify its internals
  solely from the word "atomic".
- Pure-theorem surface checking already validates a proof before requesting
  `kernel_authority` through the general constructor. This is redundant proof
  discovery, not a missing user proof: retain authority from the checked proof
  instead of asking another solver to establish the same claim.

Completed loop migration:

- Kernel-owned closure scopes collect exact value and read-safety goals;
  `both { ... } and { ... }` preserves exact child identities.
- Surface planning emits completed bodies for bare closers and automatic
  preservation. Existing bodies are validated before any named-invariant
  preplanning; stale evidence is rejected, never regenerated.
- Completion binds the exact root, snapshot, premises, execution effects, and
  invariant bundle. A request flag, incomplete body, or substituted proof
  cannot authorize closure. Provisional safety goals cannot prove themselves.
- Quantified function-call presentation names only exact current or entry
  array snapshots. Original and expanded branch, old-count, permutation,
  sorting, copy3, and pointer proofs are regression-covered.
- No-continuing-edge do-while exits retain their exit classification. Negative
  termination fixtures still reach their intended decrease failures.
- Multi-size deterministic regressions cover scope creation, retention,
  validation against unrelated facts, and explicit function arguments.

Recommended remaining migration sequence:

1. The checked-event premise, common-arm-fact, and split-obligation fallbacks
   below are removed. Resource pure deltas and checked interface lowering are
   also migrated. Preserve rejection of omitted, unrelated, and wrong-arm
   evidence and the scaling tests for retained premises and local read rules.
2. Separate quantified conversion and context-free normalization from implicit
   proof construction, then migrate pure-theorem authority, call/refinement
   guards and quantities, and termination by their own evidence types.

Completion requires checking these consumers transitively, not just obtaining
a zero grep count in `contract_certification.rs`. A retained exact rule must
have named inputs and input/output-sized work; a retained planner must be
non-authoritative and its selected result checked without rediscovery.

### Checked-event theorem-premise census (2026-09-09)

Measured at `35a3d8cd` across all 26 example projects and 1,079 markdown
fixtures, including expected failures. The instrumented full gate passed,
including 2,055 unit/CLI tests; the table does not aggregate the isolated unit
test processes. Temporary counters distinguished statement/condition callers,
premise-bundle visits, exact acceptance, general attempts and results. The
original short-circuit order and proof calls were preserved. Probes and the
subsequent diagnostic denial switch were removed; this is a documentation-only
checkpoint, not a fallback deletion.

**Scope:** `checked_evidence_premises_hold` is reached through
`checked_statement_event` and `checked_condition_event` when
`check_evidence_events` checks branch-arm event trees for `CheckedExecutionBranch::check`
and `check_interface` (including nested branches). Initial event recording
instead calls `check_evidence_state_and_premises` /
`proof_evidence_unretained_premise`; that separate retained-context, obligation,
and resource-coverage chain was not dynamically censused here. Neither were
resource rewrites, observations, or interface-fact authority.

| Corpus / caller | Premise-bundle visits | Premises tested | Exact indexed acceptance | General attempts | General successes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Examples / statement | 4 | 78 | 78 | 0 | 0 |
| Examples / condition | 4 | 58 | 58 | 0 | 0 |
| Mdtests / statement | 55 | 157 | 155 | 2 | 2 |
| Mdtests / condition | 54 | 142 | 142 | 0 | 0 |
| **Total** | **117** | **435** | **433** | **2** | **2** |

All visited bundles had premises and passed this helper. There were no general
misses or exact-builtin-only acceptances. `proves_exact` first tries builtin
rules and then indexed membership; the probe classified its successful result
as indexed when `contains_assumed_exact` also succeeded. That indexed helper
can decompose conjunctions and match condition polarity, so this column is not
a claim that every whole premise is stored as one opaque key. These are visits,
not unique theorems or unique logical premises; a bundle acceptance alone is
not proof that all later event/source checks succeed.

Only `owned-vector` and `perpetual-service` among the examples reached this
helper, and both used indexed facts exclusively. Twenty-two mdtests reached it.
The entire general-success group is
`mdtests/c_step_contract_frontier_branch.md`: two statement bundles, one for
each arm of a C `if`, invoking the same callback with `step(Buffered)`.
Bounded operand diagnostics confirmed both missing premises are exactly
`ConditionIs(Bitvector32SignedGreaterEqual(Constant(1), Constant(1)), true)`.
They require no ambient premise or nontrivial arithmetic derivation. The exact
builtin path recognizes an already reduced `ConditionTerm::Constant`, but does
not reduce this literal comparison itself.

The focused positive run passed and reproduced both general successes. A
temporary switch that rejected only this helper's general fallback made the
unchanged fixture fail promptly at `invoke.contract` proof step 2:
`checked C branch join rejected: a branch arm theorem trace does not follow its
exact C source`. This confirms a dependency in the current corpus, not merely
an unused successful search attempt. The switch was not retained, and the
expected-pass fixture, its C, and its proof were not changed.

**Implementation complete:** `checked_evidence_premises_hold` preserves its
existing exact/builtin path and otherwise checks only a literal int32 comparison
with `ground_comparison_premise_holds`. The general `proves` fallback is deleted.
The new rule checks signed `<`, `<=`, `>`, `>=`, and bitvector equality, accepting
only two literal operands and the correct requested truth polarity. It casts
the stored bits to signed int32 for ordering; it does not fold expressions,
inspect ambient facts, or call a derivation builder. It is a fixed local check,
not a new arithmetic planner or a special case for `1 >= 1`.

Regressions cover both polarities of all five comparisons over minimum/maximum
signed values, -1, 0, and 1; unsupported compound operands; missing/unrelated
symbolic premises; exact supplied premises; and rejection of `x >= 0` when only
`x > 0` is retained (even though the general prover can derive the former).
The unchanged callback fixture verifies, expands, and independently rechecks.
No new proof-object payload or user proof bookkeeping is introduced.
Nontrivial future derived premises must be planned and retained explicitly.
Initial event recording and other event/resource/interface boundaries remain
outside this completed slice.

### Resource-delta and branch-interface census (2026-09-09)

Measured at `3a1a376a`, after landing the theorem-premise migration, across
26 example projects and 1,095 markdown fixtures, including expected failures.
Both fixture gates passed. Temporary probes counted only the general-prover
calls at these event boundaries, preserving their original results. They
classified a successful call by the existing `proves_exact` checker first,
then literal comparison, then remaining derivation. The probes and denial
switch were removed before committing.

| Resource pure-delta fallback | Examples | Markdown fixtures | Successful route |
| --- | ---: | ---: | --- |
| `CheckedResourceRewrite::check` | 18 | 2 | All 20 require derivation of loadability; none pass `proves_exact`. |
| `CheckedResourceObservation::check` | 11 | 23 | All 34 pass `proves_exact`; no remaining derivation dependency. |

These are fallback attempts after the explicit allowed-fact and resource-
composition checks, not counts of all events. The separate resource-instance
rewrite path is not included: it already checks its selected delta directly.
The rewrite dependencies are `binary-tree` (4), `owned-string` (4),
`owned-vector` (10), and `c_chained_field_access.md` (2). Denying only the
rewrite-derived route makes `binary-tree` fail promptly in
`tree_rotate_left.contract` at `unfold`, with an unchecked pure-fact delta.
This is an actual dependency, not merely an observed call.

**Pure resource-delta migration complete:** observation uses exact availability
instead of its general fallback. Rewrites preserve direct body-fact membership,
exact context availability, and the existing resource-composition check, then
retain a completed local proof for any additional delta. The observed read
dependencies name the exact same address and byte count at different memory
snapshots. Their proof is an implication from one explicitly instantiated body
read premise to the destination read. The checker compares block extents and
pinned allocation-retirement metadata; it does not compare stored values,
search for arithmetic/alias proofs, or walk memory history. Nonempty retirement
metadata must share storage; two empty retirement sets match directly. Changed
retirement metadata is conservatively rejected, not searched around.

The premise index is built once over the explicit allowed body facts, using
exact address/width and a shallow, pinned lifetime identity rather than entire
memory snapshots. Completion retains the implication and checks its exact
source/conclusion binding, without reconstructing a proof. Unit tests also
exercised a reflexive equality delta absent from the fixture census; it now has
a completed intrinsic proof rather than a general-prover result. Checked
load-equality evidence remains unchanged. No C or example proof-body changes
are needed for this migration.

Regressions reject unrecorded logical consequences, missing read premises,
changed widths/addresses/extents, retired allocations (including external
allocations whose broad block survives `free`), and substituted completed
goals. A unit-only alias case (`unfold(cell(right))` with `cell(left)` and
`left == right`) also needs an exact pointer-equality premise. A unique body
read or containment range can retain that premise and a completed substitution
implication; ambiguous candidates are not searched. The containment rule keeps
the parent, range bounds, and element width exact. No resource ownership is
created by this substitution. Four-size curves cover explicit premise indexing,
unrelated memory blocks, and unrelated facts around the exact equality lookup.
Broader resource matching, ownership, and definition-evaluation
checks are **not** claimed search-free by removing these two delta fallbacks.

The expansion audit also exposed a pre-existing failure at the deferred
`simp` in `vector_copy`'s explicit preservation body (reproduced at `461bad5b`).
The deferred driver never activates the old capture flag, so completion now
matches the selected proof site and source index directly, as explicit steps
already do. A regression expands that original occurrence and independently
rechecks the resulting `vector_copy` proof.

| Branch general-prover site | Calls | Exact-check successes | Other successes | Rejected queries |
| --- | ---: | ---: | ---: | ---: |
| Common successor fact, after direct arm lookup | 27 | 0 | 2 | 25 |
| Interface proposition | 78 | 73 | 5 | 0 |
| Interface lowering facts | 6 | 0 | 6 | 0 |
| Interface lowering obligations | 6 | 0 | 6 | 0 |
| Split-path obligations | 0 | 0 | 0 | 0 |

The two common-fact successes are reflexive int32 equalities in
`proof_mark_survives_branch_join.md`; neither needs contextual search.
Rejected common-fact queries normally fall through to the explicit interface
or resource export rules and are not fixture failures. The interface-proposition
dependencies occur in `perpetual-service`, `proof_branch_pointer_local.md`,
and `step_nested_branches.md`. The lowering-fact and loadability-obligation
dependencies occur in `perpetual-service` and
`proof_branch_memory_continuation.md`.

**First branch migration complete:** common successor facts and split-path
obligations now require evidence available in each named arm, using indexed
exact checks plus context-free literal comparison and int32 reflexivity.
Neither site invokes the general prover. Tests reject a merely derivable
missing obligation, evidence present only on the other arm, omitted arms,
and unrelated roots. A four-size deterministic regression checks availability
against growing unrelated fact histories.

**Lowering retention (2026-09-09):** each checked branch now retains three
kernel-created `CheckedInterfaceLowering` records per selected interface fact:
then arm, else arm, and abstract successor. Each stores the exact selected
lowering path (asserted proposition, generated facts, and safety obligations),
selected specification, snapshot, reference snapshot, and persistent fact root.
Successor-fact admission uses the selected successor proposition rather than
re-lowering every interface for every introduced fact. Cloning the records shares
their path payloads; regression coverage checks all three positions, missing
read safety, stale fact-root rejection, and four-size unrelated-history scaling.

**Branch-interface proof migration complete:** each retained value, generated
fact, and safety obligation now has a completed `ProofObject` leaf. Its rule
accepts an indexed exact premise, an existing direct intrinsic check, an exact
registered load definition, or a constant-byte subrange of a named read premise.
It does not call the general contextual prover. Definition witnesses match the
actual registered variable, memory, and address; reserved-variable spelling alone
is insufficient. Read premises come from the explicitly exported resources after
their existing ownership checks, indexed once per arm/successor by exact memory
and base. This is not a scan of ambient resources or a new ownership prover.

The surface's two-arm, decided-arm, and terminal-arm assertion checks are exact
as well. Optional entry-loadability export no longer invokes general proof.
The few assertions formerly derived implicitly now have explicit `have` bodies
in the unchanged example and regression C programs. The nested arithmetic body
is expanded to a named theorem application. No new proof syntax was needed.

Regressions reject merely derivable assertions, missing safety proofs, wrong
load identities/addresses/snapshots, stale fact roots, and incomplete retained
proof bundles. Four-size curves cover persistent premise retention and indexing
the explicit resource clauses. The original branch fixtures verify and their
expansions recheck. The `perpetual-service` frame round-trip also exposed and fixed
printing population patterns with a `view` qualifier, which is not count syntax.

The pure resource observation/rewrite deltas above are now migrated as well.
**Next:** quantified conversion and context-free normalization, followed by the
other authority consumers in the inventory. Broader resource matching/ownership
and definition-evaluation rules remain separate work.

### Quantified-conversion census (2026-09-09)

Measured at `423a4e9a`, after resource pure-delta migration, in an isolated
worktree/build directory. Temporary probes in
`quantified_equivalent_available_fact` counted candidate comparisons, not proof
sites or all quantified lookups. Ordinary verification covered 25 example
projects (the existing `multifile-registry` quarantine excluded) and 1,118
markdown fixtures, including expected failures. Both fixture gates passed.

| Corpus | Exact/current binder match, both simp directions succeed | Beyond current binder match, both succeed | Only one direction succeeds | Neither succeeds |
| --- | ---: | ---: | ---: | ---: |
| Examples | 4 | 0 | 0 | 3 |
| Markdown fixtures | 107 | 17 | 28 | 130 |

All 28 one-way comparisons succeeded only in the reverse direction and were
correctly rejected by the mutual-equivalence helper. The 17 successful
nontrivial-to-the-current-matcher comparisons occur in just three fixtures:

- `copy_n_segment_invariant`: one kernel `matching_quantified_facts` success,
  reached by `apply_assumption` while smart closure tries its simple steps.
- `fill_tail_old_prefix_segment`: two surface smart-premise syntax matches.
- `loop_sorted_range_invariant`: two kernel matches while fixed-state loop
  initialization calls `with_selected_load_equality_bridge`, plus twelve
  surface smart-premise syntax matches.

The fourteen surface matches all come from
`smart_closures.rs::available_surface_fact`'s local `matches_kernel`
closure; they select a surface form
for a kernel premise rather than independently closing a kernel goal. Targeted
runs with caller/stack probes distinguished those uses from the three
kernel matches. A successful fallback attempt does not establish that the
fixture needs it: another checked planning route may still work when denied.

Static authority/consumer inventory:

- `ProofFacts::matching_quantified_facts` filters an indexed bucket using the
  one-binder matcher, then mutual simp. It feeds pure `assumption`,
  cross-effect availability/matching, `apply_instantiate`, and selected-load
  bridge setup. `matching_quantified_fact` currently collects all matches
  before taking the first; migration should avoid retaining this unnecessary
  whole-bucket proof search.
- Surface pure/fixed-state `instantiate using` and `transport using` checks
  call the helper directly to recognize listed facts. Smart goal closure may
  turn its answer into an `Assumption` proof step. These are not all merely
  optional premise-selection heuristics.
- Other surface uses select/recover snapshot-qualified syntax, match atomic
  or restricted-simp targets, and omit an already-instantiated quantified
  premise. `pure_fact_is_available` also uses it for the surface implication
  extraction checker. Audit callers when changing the shared helper, not just
  the kernel bucket filter.

Two different notions must stay separate. `quantified_binder_equivalent`
substitutes the outer binder and compares the body; it does not cover all
nested quantifier/range-fold alpha-renaming. The existing
`QuantifiedEquivalenceKey` handles nested binders, but deliberately **omits load
memory snapshots**. Key equality is candidate selection, not proof authority;
accepting it directly could identify facts before and after a write. A
replacement structural matcher must preserve free-variable identities,
capture avoidance, sorts, and exact load/snapshot identity, with no contextual
memory or logical reasoning hidden inside it.

**Denial experiment:** replace the shared helper's mutual simp with only exact
equality or the existing binder matcher, leaving all other planning/checking
paths intact. All 25 examples and 1,118 markdown fixtures still pass their
expected verdicts, without any proof-body or C edits. Across the 2,081 unit/CLI
tests, the semantic failure is
`quantified_check_key_canonicalizes_range_fold_binders`: it expects a universal
containing a range fold to match after renaming the universal, accumulator, and
item binders. The temporary environment-controlled probe also trips the
intentional `kernel_source_reads_no_environment_variable` source-policy test;
that is an instrumentation artifact, not a dependency on conversion. Neither
probe nor denial switch is retained. These results concern ordinary fixture
verification and existing unit/expansion tests, not an exhaustive corpus audit
of all smart expansion sites or quarantined examples.

Recommended implementation order:

1. Add a search-free, capture-safe structural alpha matcher covering nested
   quantifiers and range-fold binders, while preserving exact snapshot/load
   identities. Keep the snapshot-blind index only for candidate selection.
   Pin renamed-binder positives and changed-free-variable, capture, changed
   snapshot/store, sort, and logical-conversion negatives. Include multi-size
   deterministic work tests over binder depth and unrelated context facts;
   ordinary single-match availability should not collect every candidate.
2. Replace mutual simp in the shared availability helper and kernel matching
   with that structural rule. The denial census does not currently require
   any fixture proof edits or a new proof construct. Existing smart planners
   already find alternatives in the three observed fixtures; retain and audit
   those emitted proof bodies rather than promoting an index hit to authority.
3. Run the full gate and targeted expansion audits for the three named fixtures
   plus nested-binder/instantiation regressions. If a genuine conversion is
   needed, construct it with explicit introductions, instantiation, rewrites,
   or transport and retain that proof; do not restore a boolean simp fallback.
   Then proceed to the separate context-free-normalization census.

### Pointer-offset effect-equality census (2026-09-09)

Measured at `6f0fdf7a`, after the loop back-edge migration, across all 26 example
projects and 1,073 markdown fixtures (including expected failures). Temporary
caller-tagged counters in `c_pointer_offsets_proven_equal_for_effect` distinguished
entry, interruption, exact normalized equality, restricted equality, and the
final `assumptions.proves(PointerOffsetEqual)` attempt/result. Each fixture
reported its counters after its serial verification completed. The probes were
removed; this census changes no runtime behavior.

| Corpus / immediate consumer | Helper calls | Exact successes | Restricted successes | General fallback attempts | General fallback successes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Examples: Surface effect checking | 147 | 0 | 1 | 146 | 0 |
| Examples: kernel resource-pointer matching | 7 | 0 | 0 | 7 | 0 |
| Mdtests: Surface effect checking | 185 | 0 | 0 | 185 | 0 |
| Mdtests: kernel resource-pointer matching | 4 | 0 | 0 | 4 | 0 |
| Both corpora: contract store-chain comparison | 0 | 0 | 0 | 0 | 0 |
| **Total** | **343** | **0** | **1** | **342** | **0** |

All 342 general fallback attempts returned false. No instrumented interruption
exit occurred. The one restricted success was in `examples/perpetual-service`;
its other seven calls missed. Resource-pointer fallback attempts came from
`binary-tree` (2), `owned-segmented-buffer` (2), `ring-buffer` (3), and one each
from `c_chained_field_access`, `composite_resource_owned_buffer_get`,
`composite_resource_owned_buffer_set`, and
`return_population_rejects_unupdated_sibling` mdtests. The direct
`memories_equal_by_execution_provenance` store-chain caller was not reached.
Counts describe immediate consumers, not all transitive callers or unique
logical queries. The instrumented full gate passed, including 2,043 unit/CLI
tests; those isolated unit processes are not included in the table.

**Deletion complete:** only the final `assumptions.proves` disjunct is removed.
Exact-load normalization, restricted equality, all three deadline checks, and
retained load-equality evidence are unchanged. Focused regressions cover exact
stored-load normalization, explicit offset-equality facts, unequal constants,
missing and unrelated offset facts, and expiry even on identical offsets.
A distinguishing negative test supplies an inconsistent context: the general
prover can establish the queried equality, but this helper now rejects it
without a direct/restricted justification. No new witness type is introduced.
The earlier census was observational; deletion and these regressions are the
subsequent implementation. This does not classify the internals of the
restricted checker as fully migrated, nor remove other effect/resource proof
discovery.

## Pointer-distinctness disposition

The general `pointers_proven_distinct` fallback and exported
`prove_memory_load_after_store_distinct_under_assumptions` constructor are
deleted. There is no compatibility interval for this low-level API. Keeping a
constructor that accepted an ambient `PureFactContext` would have preserved
proof discovery inside the authoritative kernel; silently narrowing it would
also have left callers with an opaque completeness change.

The internal `pointers_proven_distinct_for_memory_resolution` remains. Its
rules are limited to exact block identity, offset cancellation or disequality,
an exact pointer-equality fact, and explicit range evidence, all bounded by the
pointer query and indexed evidence. Memory-load evaluation and whole-snapshot
comparison now use only that narrower predicate for distinctness.

## Implementation order

1. **Complete:** correct the inventory and operational definition in this issue.
2. **Complete:** delete the general pointer-distinctness fallback, its exported
   contextual constructor, and route-specific tests.
3. **Complete:** replace the directly owned structural and fixed-point cuts
   with complete input-sized walks, landing a scaling regression with each
   change. Exact-load traversal, havoc write-set identity, and nested-binder
   comparison and the canonicalization family are complete. The arithmetic
   depth cut is separately deferred to the smart-tactic migration in
   `issues/arithmetic.md`.
4. **Complete:** move upper-bound split selection to a surface planner that
   emits checked proof branches; delete the kernel rule and depth limit.
5. **Complete:** delete general finite context splitting and its numeric cap.
   Singleton ranges now use an exact checked substitution naming two indexed
   bound facts; the sole multi-value dependency was replaced by direct symbolic
   array-index bounds reasoning, so no surface case planner was needed.
6. **Complete:** retain finite typed load-equality evidence, delete the global
   framed-load prover, prevent arbitrary term-pair recursion, and remove the
   load-equality depth limit.
7. **Complete:** the dead atomic load-equality fallback and boolean
   flag are deleted; the alias-refutation rule remains without its unobserved
   broad boolean tier; and `SimpFactReasoningGuard` cycles advance the epoch so
   they cannot poison enclosing negative memos. The epoch is renamed and all
   31 deadline checkpoints record incomplete reasoning, with outer limit-error
   propagation audited above. `inside_condition_decision` is memo-scope policy, not an
   answer-suppressing tier.
8. **Audit complete; implementation open:** migrate the general-prover authority
   consumers in the inventory above. Loop back-edge closure and
   resource-invariant theorem constructors are complete. The remaining
   boundaries include event/fact availability, normalization, pure theorems,
   call/refinement conditions, and termination. Preserve the stated
   invariant; do not relabel internal proof construction as checking.

Each numbered step should be a coherent green change. A later step must not be
used to excuse an opaque bound introduced by an earlier one.

## Method

To retake a census, add a temporary `record_reasoning_route("...")` counter (a
static mutex map in `src/instrumentation.rs`) at each site, have
`tests/mdtests.rs` and `tests/examples.rs` print the map after the run, and run
both harnesses with `-- --nocapture`. The probes must not land. Record both how
often a route is attempted and how often it is the first route to decide the
query; attempts alone do not justify retaining a fallback.

To compare cost without the machine's load, run `click profile <example> --top
40 --time-limit 300s` on a throwaway checkout of the parent commit and on the
branch and compare deterministic-work aggregates, not wall time.

Lessons a fresh agent should not relearn: build an in-progress guard with
`bool::then(|| Guard)`, never `then_some(Guard)`, since the eagerly built
guard's drop unregisters the outer query on the cycle path; distinguish a long
acyclic walk from a repeated query; when removing a bound slows a harness, first
check whether the replacement accidentally scans or clones ambient state; and
do not expand or profile a target whose ordinary verification has not
completed, except when the timeout itself is the tooling bug under study.

## Intended regression

For every structural bound replaced, add a deterministic scaling regression
over several input sizes showing work bounded by the complete named input. For
every query guard, add a unit test showing that an identical query refuses
re-entry without unregistering its outer query and that distinct queries nest.
For every search moved outward, verify both the generated/expanded explicit
proof and the kernel check of that proof, including rejection of a missing,
reordered, or unrelated premise. Retain the fixture harnesses and the
contract-fallback census at zero.

The havoc identity regression must contain two structures that share their
first 64 levels but differ below that point and show that their identities and
checked endpoints remain distinct. Deadline regressions must show a distinct
limit error and no reusable negative memo entry.

## Not in scope

- Smart tactics and search in the surface; they produce checked proof steps or
  explicit certificates, which is where search belongs.
- Execution path-width, loop-unroll, call-depth, and deterministic smart-tactic
  work budgets whose units and failures are explicit.
- Memo capacity and eviction policy when eviction cannot affect correctness or
  completeness.
- Performance work on an exact, relevant-input-bounded rule unless a scaling
  regression shows that the classification is wrong.

Completed kernel-API hardening is not reopened wholesale, but a depth-truncated
value advertised as a lossless certificate identity is in scope here because
the bound can change what the checker accepts.

## Acceptance criteria

- No authoritative result under `src/kernel/` depends on a fuel counter or
  numeric depth cut.
- Every structural walk is complete over its named input, cycle-safe where
  necessary, and covered by a deterministic multi-size scaling regression.
- General finite context splitting and its numeric cap are deleted. Singleton
  substitution retains only its two indexed bound facts and child proof, and
  symbolic array access uses direct endpoint checks. The upper-bound split is
  surface planning with explicitly checked branches. No checked operation
  clones or scans the complete context merely to validate a split.
- Global load equality is decided from typed evidence retained by the proof
  object. Its migration covers fact matching, transport, contract
  certification, loops, resources, and other kernel consumers. Any
  surface-expressible expansion remains a certificate in the narrower sense.
- General pointer distinctness and its exported theorem constructor are
  deleted; no retained constructor discovers a proof by ambient global
  fallback.
- The dead atomic load-equality route and its broad flag are gone. Alias
  refutation retains no broad reentrancy flag. Exact-query cycle cuts cannot
  poison a negative memo, and the incompleteness epoch is deleted or named and
  documented for every cause it actually records. Nested memo-scope policy is
  not classified as answer suppression.
- Deadline expiry propagates as a verification-limit error rather than an
  ordinary proof miss and cannot populate a negative memo.
- Certification decides by matching recorded completions and exact rules;
  `PureFactContext::proves` is not called from
  `src/kernel/api/contract_certification/`.
- Authoritative uses of the general proposition prover are removed, supplied
  explicit checked evidence, or listed as deliberate exceptions that narrow
  the issue's top-level invariant.
- No speculative/global proof-search fallback and no `std::env` read remains
  under `src/kernel/`.
- `scripts/check.sh` passes, both fixture harnesses pass with the
  contract-fallback census at zero, and deterministic work over the profiled
  examples does not rise.
