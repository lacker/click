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

The earlier claim that every structural depth cut was gone was incorrect. The
inventory below is the current boundary as of 2026-09-03. The load-equality
depth of two (`MEMORY_LOAD_EQUALITY_DEPTH_LIMIT`) remains separately measured
and designed in `issues/load-equality-prover-in-kernel.md` because it caps a
fact-branching search rather than a structural walk.

The first two ordered changes are complete. This issue now states the
operational boundary and corrected inventory, and the unused general pointer
distinctness fallback has been deleted. Click has no compatibility commitment
for the low-level kernel API, so its contextual theorem constructor was deleted
with it rather than deprecated or replaced with a compatibility shim. Memory
resolution retains only its narrower exact, query-bounded distinctness check.

Structural cleanup is now partially complete. Exact-load materialization and
normalization follow complete acyclic chains with exact cycle detection, using
iterative term reconstruction where nesting can be deep. Call-havoc write-set
markers now use a complete iterative, length-delimited structural encoding;
two write sets that first differ below the former depth limit produce distinct
memory endpoints. Both walks have multi-size deterministic-work regressions.

## Current inventory

Counts below are examples / mdtests, times the bound or route fired, measured
2026-09-03 where a count is given.

### Structural and fixed-point cuts

These are not surface-search migrations. Replace each cut with work bounded by
the complete named structure, plus an exact cycle check or an iterative walk as
needed.

1. **Arithmetic interval term depth**, `ARITHMETIC_INTERVAL_DEPTH = 32`
   (`src/kernel/proof/fact_reasoning.rs`). `signed_term_interval` silently
   returns no interval for a deeper arithmetic term. Walk the complete term
   iteratively and add a multi-size deep-term scaling regression.
2. **Alternating canonicalization rounds**, `CANONICALIZATION_ROUNDS = 3` in
   `src/kernel/assumptions.rs`. The result can depend on how many times
   simplification and equality-class selection alternate. Replace it with a
   fixed point that has an explicit monotone measure or cycle check, or define
   one canonical representation computed directly.
3. **Canonical order endpoint depth**, `CANONICAL_ORDER_ENDPOINT_DEPTH = 6`
   in `src/kernel/assumptions/proposition_reasoning.rs`. This affects the
   endpoint keys used by context-inconsistency reasoning. Traverse the complete
   endpoint and preserve the bucketing/scaling property with regressions.
4. **Deep-term canonicalization preflight**, `bitvector_term_deeper_than(...,
   64)` in `src/kernel/api.rs`, used to skip canonicalization in proposition
   reasoning. If the purpose is stack safety, make the canonicalizer iterative;
   a depth predicate must not decide whether an otherwise supported fact can
   be proved.
5. **Nested quantified-binder comparison**, called with depth eight from
   surface theorem application but implemented in
   `src/kernel/proof/fact_reasoning.rs`. It is a generation-side recognizer, not
   theorem authority. Move it to the surface or make the structural comparison
   complete; do not leave a literal exception hidden under `src/kernel/`.

`ATOMIC_PREMISE_MINIMIZATION_DEPTH` (`src/kernel/assumptions.rs`) and
`VERIFICATION_SESSION_DEPTH` (`src/kernel/mod.rs`) are nesting-state flags, not
logical cuts. Cache-size constants are eviction policy, not completeness
bounds. Neither category is part of the list above unless it is later shown to
change an answer.

### Search and tiering

1. **The upper-bound split**, `UPPER_BOUND_SPLIT_DEPTH_LIMIT = 1` in
   `derive_by_upper_bound_split`. Fired 11 / 46. It chooses an ambient upper
   bound, splits `k < b` versus `k == b`, and re-enters the whole prover in both
   branches. A surface smart closer should select the bound and emit a checked
   proof `if k < b`; the other arm obtains equality from the recorded bound and
   `not(k < b)`. The kernel already checks complementary proof-`if` branches.
2. **The finite context split**, `FINITE_CONTEXT_SPLIT_LIMIT = 8` in
   `src/kernel/reasoning/order_reasoning.rs`, used by proposition reasoning and
   its derivation checker. Fired 8 / 840; an earlier census found it deciding
   0 / 20 goals. A surface planner may emit nested proof `if x == value`
   branches, or a new explicit finite-case certificate whose checker is linear
   in the listed cases. The certificate must name only the range evidence and
   branch proofs: the current `FiniteContextSplit` stores the entire context,
   which violates relevant-input scaling.
3. **Global load equality**, `MEMORY_LOAD_EQUALITY_DEPTH_LIMIT = 2`, and the
   framed-load fallback from `memory_loads_proven_equal`. It hit 345,653 /
   315,061 times in its census. This is owned by
   `issues/load-equality-prover-in-kernel.md`. Its migration must cover every
   kernel and surface consumer, not only fact matching: planning selects an
   effect/DAG route, and a typed certificate records the route and per-edge
   framing evidence for linear checking. The existing surface `transport`
   checker still calls global load equality and is not yet that boundary.
4. **Coarse reentrancy tiers**: `bounded_snapshot_comparison_active` around
   snapshot aliasing, `inside_condition_decision` around condition decisions,
   `ENDPOINT_BRIDGE_ACTIVE`, `LOAD_EQUALITY_RESOLUTION_ACTIVE`,
   `ALIAS_GUARD_REFUTATION_ACTIVE`, and `DERIVATION_WALK_ACTIVE`. These suppress
   every nested query rather than only an identical in-progress query. Remove
   them with their owning search, or replace a genuinely structural recursion
   with a guard keyed by the exact query.
### Incomplete-answer and authority audit

1. **`search_truncations` and negative-memo gating**. The counter currently
   records more than search: exact-query cycle cuts, wall-clock deadlines,
   load-equality depth refusal, and coarse tier suppression. While incomplete
   answers remain, rename it to describe that role (for example,
   `incomplete_reasoning_epoch`) rather than documenting it as cycle-only.
   Audit every conservative early return, including `SimpFactReasoningGuard`,
   so a path-dependent negative is never cached. Delete the mechanism only when
   incomplete nested answers cannot reach a memo boundary.
2. **Deadline checks**, currently 35 `deadline_exceeded` sites under
   `src/kernel/`. Deadlines are separate from deterministic tactic budgets, but
   they are not harmless if a helper's `false`/`None` is observed as an ordinary
   proof miss. Audit propagation so expiry becomes a distinct verification
   abort and no negative result produced after expiry is memoized.
3. **Authoritative callers of the general proposition prover**. Removing the
   two split rules does not by itself establish "the kernel does not search."
   `verify_lowered_invariant_path` in `src/kernel/loops.rs` calls
   `derive_proposition_without_premise_minimization`, and
   `theorem_from_contextual_proof` in `src/kernel/api.rs` searches for a
   derivation and issues a theorem from its selected premises. Inventory the
   remaining callers and either move their planning to the surface, replace
   them with named checked evidence, or explicitly narrow this issue's claimed
   invariant. Contract certification's existing ban on
   `PureFactContext::proves` is necessary but not a complete authority audit.

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
3. **In progress:** replace the structural and fixed-point cuts with complete
   input-sized walks, landing a scaling regression with each change. Exact-load
   traversal and havoc write-set identity are complete; the five items still
   listed above remain.
4. Move upper-bound split selection to a surface planner that emits checked
   proof branches.
5. Move finite context splitting to explicit surface branches/certificates and
   remove the whole-context derivation payload.
6. Complete the separately measured load-equality certificate migration.
7. Remove coarse reentrancy tiers and audit deadline propagation, cycle cuts,
   and negative-memo gating; then delete or accurately rename the incompleteness
   epoch.
8. Finish the authoritative general-prover caller audit, or narrow the stated
   invariant with an explicit rationale for any retained kernel planner.

Each numbered step should be a coherent green change. A later step must not be
used to excuse an opaque bound introduced by an earlier one.

## Method

To retake a census, add a temporary `record_reasoning_route("...")` counter (a
static mutex map in `src/instrumentation.rs`) at each site, have
`tests/mdtests.rs` and `tests/examples.rs` print the map after the run, and run
both harnesses with `-- --nocapture`. It takes about an hour to reapply and must
not land. Record both how often a route is attempted and how often it is the
first route to decide the query; attempts alone do not justify retaining a
fallback.

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
  numeric depth cut. `MEMORY_LOAD_EQUALITY_DEPTH_LIMIT` may remain only while
  `issues/load-equality-prover-in-kernel.md` is open; no new tier replaces it.
- Every structural walk is complete over its named input, cycle-safe where
  necessary, and covered by a deterministic multi-size scaling regression.
- The finite context split and upper-bound split are surface planning whose
  selected cases are checked explicitly, or are deleted. No checked operation
  clones or scans the complete context merely to validate the split.
- Global load equality is decided from recorded evidence. Its typed certificate
  and migration cover fact matching, transport, certification, loops,
  resources, and other kernel consumers.
- General pointer distinctness and its exported theorem constructor are
  deleted; no retained constructor discovers a proof by ambient global
  fallback.
- Coarse reentrancy tiers are gone. Exact-query cycle cuts cannot poison a
  negative memo, and the incompleteness epoch is deleted or named and
  documented for every cause it actually records.
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
