# Remove search, fuel, and fallbacks from the kernel

## Violated invariant

The kernel checks; it does not search. A kernel decision is decided by
rules whose work is bounded by the inputs they name, it never depends on
a fuel counter or a depth cut, and it never tries a broader route after a
narrower one fails. Search belongs to the surface's smart tactics, whose
results are certificates the kernel then checks.

The working rule for the remaining items: when a bound sits on a walk
over a well-founded structure (a chain of DAG edges, a term, an equality
class, a fact's disjuncts), it is replaced by the structure itself, with
a cycle check where the walk can revisit a node. When a bound caps a
search, whose branching factor is the number of facts rather than the
size of the query, no counter-free replacement inside the kernel exists,
and the fix is to move the search into a surface tactic that records a
checkable fact. Tuning a tier or a memo until a search looks cheap enough
is not a fix; it is the bound under another name.

## Status

The dead routes, the surface's second lowering and evaluators, the
artifact-less body execution, the environment switches, the ladders that
answered one question twice, prover 1's handoff from certification, and
every fuel counter or depth cut on a walk are gone from the kernel (the
last of them on 2026-09-03). Walks that can revisit a node carry an
in-progress cycle check on the query instead: `ResolutionQueryGuard` in
`src/kernel/reasoning/memory_resolution.rs` is the pattern, with nested
queries going through the memo. Enumerations the query's own inputs bound
(quantifier instances, disjuncts, fold steps) are charged as
deterministic work per instance. Deterministic work over the profiled
examples fell or held at every step.

What is left caps searches, not walks. One search is carved out: the
load-equality depth of two (`MEMORY_LOAD_EQUALITY_DEPTH_LIMIT`,
`src/kernel/assumptions.rs`) is owned by
`issues/load-equality-prover-in-kernel.md`, with the measurements that
show why no kernel-side replacement works.

## What remains

Counts are examples / mdtests, times the bound fired, measured 2026-09-03.

1. **The finite context split**, `FINITE_CONTEXT_SPLIT_LIMIT = 8`
   (`src/kernel/reasoning/order_reasoning.rs`; used by
   `derive_by_finite_context_split` and `proves_by_finite_context_split`
   in `src/kernel/assumptions/proposition_reasoning.rs`, and by the
   derivation checker in `src/kernel/assumptions.rs`). Fired 8 / 840.
   Prover 1 splits the context on a variable with a finite range and
   proves the goal once per value; the cap refuses ranges wider than eight.
   The split is a case analysis the surface should state (a `cases`
   tactic recording one certificate per value); the kernel then checks
   the cases it is given. An earlier census found the split deciding
   0 / 20 goals.
2. **The upper-bound split**, `UPPER_BOUND_SPLIT_DEPTH_LIMIT = 1`
   (`derive_by_upper_bound_split`, same file). Fired 11 / 46. Splits a
   goal on `k < b` versus `k == b` and re-enters the whole search in both
   halves; its own comment records that a depth of two cost
   `bubble_sort3_two_pass_sorted` 20 s for nothing. Same remedy as 1.
3. **Reentrancy suppressions around snapshot comparison**:
   `bounded_snapshot_comparison_active` and `inside_condition_decision`
   gating the general alias legs in `src/kernel/reasoning/memory_resolution.rs`
   and `src/kernel/assumptions/memory_reasoning.rs`, and the
   `ENDPOINT_BRIDGE_ACTIVE` lock in `src/kernel/primitives/resource_algebra.rs`.
   Fired 2 / 364. Each is a tier: a nested query gets the cheap legs, a
   top-level one the prover. They exist because the load-equality prover
   re-enters itself, so they go with `issues/load-equality-prover-in-kernel.md`.
4. **`search_truncations` and the memo gating that reads it**
   (`note_search_truncation` in `src/kernel/assumptions.rs`, read by the
   decision, resolution, unchanged-load, and inconsistency memos). The
   cycle checks note a truncation when they refuse re-entry, so that a
   negative answer weakened by a cycle is not cached; that use is
   legitimate and stays as long as cycle checks exist. Delete the counter
   only when items 1 to 3 and the carved-out prover are gone and the
   cycle-cut answers are shown never to be cached, or rename it to say
   what it now records.
5. **Deadline checks**: 35 `deadline_exceeded` sites across
   `src/kernel/`. A wall-clock limit, not a search bound; tactic budgets
   are enforced in deterministic work units. Whether the kernel should
   observe wall time at all is a separate question from this issue's,
   and the checks are harmless to it.
6. **General pointer distinctness** (`pointers_proven_distinct`,
   `src/kernel/reasoning/memory_resolution.rs`) never decided anything
   over the corpus (38 / 778 queries) but is pinned by kernel unit tests
   and costs nothing measurable. Delete it with its tests, or keep it as
   an exact rule; either is fine.

`ATOMIC_PREMISE_MINIMIZATION_DEPTH` (`src/kernel/assumptions.rs`) is a
nesting flag that disables premise minimization inside itself, not a cut.

## Method

To retake a census: add a temporary `record_reasoning_route("...")`
counter (a static mutex map in `src/instrumentation.rs`) at each site,
have `tests/mdtests.rs` and `tests/examples.rs` print the map after the
run, and run both harnesses with `-- --nocapture`. It takes about an
hour to reapply and must not land. To compare cost without the machine's
load, run `click profile <example> --top 40 --time-limit 300s` on a
throwaway checkout of the parent commit and on the branch and compare
the deterministic-work aggregates, not the wall time.

Lessons a fresh agent should not relearn: build an in-progress guard
with `bool::then(|| Guard)`, never `then_some(Guard)`, since the eagerly
built guard's drop unregisters the outer query on the cycle path; when a
bound is removed and the harness slows, the replacement was not
structural, so census the site rather than tune it; and nested queries
must be memoized once fuel is gone, since the memo used to refuse
anything computed under fuel.

## Intended regression

For every bound replaced, a deterministic scaling regression over several
input sizes showing the replacement's work is bounded by its inputs
(`docs/internals/verification-efficiency.md`); a kernel unit test that
each guard refuses re-entry without unregistering the outer query; and
the fixture harnesses with the contract-fallback census at zero. The
regressions for the bounds already replaced are in `src/kernel/tests/`
and beside the guards they pin.

## Not in scope

- Smart tactics and search in the surface; they produce certificates the
  kernel checks, which is where search belongs.
- Completed kernel-API soundness hardening; it is independent of this
  search-and-fuel cleanup.
- Performance work on rules that are already exact.

## Acceptance criteria

- No fuel counter or depth cut under `src/kernel/`, except
  `MEMORY_LOAD_EQUALITY_DEPTH_LIMIT`, whose removal
  `issues/load-equality-prover-in-kernel.md` owns; every bounded rule's
  bound is a function of the inputs it names, with a scaling regression.
- The finite context split and the upper-bound split are either surface
  tactics whose cases the kernel checks, or deleted; no kernel rule
  issues a theorem by search.
- `search_truncations` is deleted, or documented as recording cycle cuts
  only.
- Certification decides by matching recorded completions and by exact
  rules; `PureFactContext::proves` is not called from
  `src/kernel/api/contract_certification/`.
- No route in the kernel tries a broader method after a narrower one fails
  on the same question, and no `std::env` read under `src/kernel/`.
- Both fixture harnesses pass with the contract-fallback census at zero;
  deterministic work over the profiled examples does not rise.
