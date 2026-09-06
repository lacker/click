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

The 2026-09-05 deciding-route census refined that older depth-hit count. After
all cheaper load-equality rules had failed, the global fallback proved only 31
of 1,628 example queries and 27 of 1,347 mdtest queries. Those 58 decisions are
now classified by fixture, consumer, load, and required replacement evidence
in the dedicated issue; 23 were merely positive-memo reuses.

The first load-equality migration slice is complete. Fixed-state restricted
`simp` now retains a snapshot-anchored `transport` when equality rewrites leave
two names for one load, and ordinary fact matching no longer invokes the
global framed-load reconstruction fallback. The input-cursor expansion checks
independently and both fixture harnesses pass. Direct framed-load consumers and
the reentrant snapshot-resolution path remain, so the depth limit cannot yet
be removed.

The second load-equality slice moved every consumer that was already decidable
from the recorded memory DAG: surface proof matching, load-variable origin
matching, loop effects, resource endpoints, and the ordinary contract
certification helpers. The special bounded-snapshot-comparison mode is now
dead and deleted. A third slice established consumer-owned equality evidence:
resource rewrites and observations retain and recheck any checked equality
they consume, and contract materialization retains its typed witnesses on the
function-claim proof object. `StoreExplicitRange` hops now retain either their
exact separation proposition or the owning resource composition, indexed
range pair, and orientation. One direct framed-transport consumer remains
because bounded-pool additionally needs a typed endpoint bridge between
sibling snapshot forms along the selected derivation path. The depth-bounded
congruence search for registered loads whose addresses themselves contain
registered loads also remains.

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

Counts below are examples / mdtests, times the bound or route fired, measured
2026-09-03 where a count is given.

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

1. **The finite context split**, `FINITE_CONTEXT_SPLIT_LIMIT = 8` in
   `src/kernel/reasoning/order_reasoning.rs`, used by proposition reasoning and
   its derivation checker. Fired 8 / 840; an earlier census found it deciding
   0 / 20 goals. A surface planner may emit nested proof `if x == value`
   branches, or a new explicit finite-case certificate whose checker is linear
   in the listed cases. The certificate must name only the range evidence and
   branch proofs: the current `FiniteContextSplit` stores the entire context,
   which violates relevant-input scaling.
2. **Global and dependent load equality**,
   `MEMORY_LOAD_EQUALITY_DEPTH_LIMIT = 2`. The fallback from
   `memory_loads_proven_equal` has been removed, but framed atomic transport
   still directly calls the global prover because its bounded-pool derivation
   path needs a typed sibling-snapshot endpoint bridge. Its
   `StoreExplicitRange` hop is now typed. The remaining depth guard hit
   345,653 / 315,061 times in the original depth census. The later
   deciding-route census found that the fallback itself answered only 31 /
   1,628 example calls and 27 / 1,347 mdtest calls. This is owned by
   `issues/load-equality-prover-in-kernel.md`. Its migration must cover that
   endpoint bridge and dependent registered-load addresses. An exact-query guard
   terminates but branches into 60,000–120,000 distinct subqueries in the
   owned-string regression, so the replacement must retain typed
   congruence/equality-path evidence rather than substitute another recursion
   tier.
3. **Coarse reentrancy tiers**: `bounded_snapshot_comparison_active` around
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
   the remaining loop and effect-certification paths still construct
   derivations from ambient facts. The former
   `theorem_from_contextual_proof` resource path is complete: its constructors
   now accept only exact recorded facts and perform no proof search. Inventory
   the remaining callers and either move their planning to the surface,
   replace them with named checked evidence, or explicitly narrow this issue's
   claimed invariant. Contract certification's existing ban on
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
3. **Complete:** replace the directly owned structural and fixed-point cuts
   with complete input-sized walks, landing a scaling regression with each
   change. Exact-load traversal, havoc write-set identity, and nested-binder
   comparison and the canonicalization family are complete. The arithmetic
   depth cut is separately deferred to the smart-tactic migration in
   `issues/arithmetic.md`.
4. **Complete:** move upper-bound split selection to a surface planner that
   emits checked proof branches; delete the kernel rule and depth limit.
5. Move finite context splitting to explicit surface branches/certificates and
   remove the whole-context derivation payload.
6. Complete the separately measured load-equality certificate migration.
7. Remove coarse reentrancy tiers and audit deadline propagation, cycle cuts,
   and negative-memo gating; then delete or accurately rename the incompleteness
   epoch.
8. Finish the authoritative general-prover caller audit, or narrow the stated
   invariant with an explicit rationale for any retained kernel planner. The
   resource-invariant theorem constructors are complete; loop and effect
   certification callers remain.

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
