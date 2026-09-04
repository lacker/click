# Remove search, fuel, and fallbacks from the kernel

## Violated invariant

The kernel checks; it does not search. A kernel decision is decided by
rules whose work is bounded by the inputs they name, it never depends on
a fuel counter or a depth cut, and it never tries a broader route after a
narrower one fails. Search belongs to the surface's smart tactics, whose
results are certificates the kernel then checks.

A working rule for the remaining items (agreed 2026-09-03): when a bound
sits on a walk over a well-founded structure (a chain of DAG edges, a
term, an equality class, a fact's disjuncts), it is replaced by the
structure itself, with a cycle check where the walk can revisit a node.
When a bound caps a search, whose branching factor is the number of facts
rather than the size of the query, no counter-free replacement inside the
kernel exists, and the fix is to move the search into a surface tactic
that records a checkable fact. Tuning a tier or a memo until a search
looks cheap enough is not a fix; it is the bound under another name.

## Status

Filed 2026-09-02 from a census of the kernel's reasoning routes over both
fixture harnesses. Slices 1 to 6 have landed, and slice 7 has landed
everything that is not a search cap:

| slice | landed | what |
|---|---|---|
| 1 | `976e8d51` | nine reasoning routes that never decided anything deleted |
| 2 | `8bfa40fa`, `a1fdf7da`, `889fb14d` | one lowering: every proof-side proposition elaborated and lowered by the kernel; the surface evaluator, legacy claim checker, second-proof route, excluded-middle arm, and C-fragment evaluator deleted; claim certification matches recorded completions over every reusable artifact's path set |
| 3 | `72490267` | artifact-less body execution deleted from certification |
| 4 | `1c21f161` | no environment variable read under `src/kernel/` |
| 5 | `c1b34163` | ladders reordered so the deciding layer runs first; the legs that never decided deleted |
| 6 | `4435f334` | prover 1 out of certification; exact rules per proposition kind |
| 7 | `79a9b574`, `8dc6282b`, `66e87b39`, `5baf00cf`, `9baa858c` | fuel and depth cuts replaced by structural bounds, see below |

Slice 7 so far. Deleted outright, with scaling regressions: the DAG hop
limits, derivation-match limit, canonicalization depth, interval depth,
load-equality term-depth precheck (walks over strictly decreasing snapshot
ids or over a term); the simp reasoning budget of 300 and simp depth of 8
(decisions are memoized and cycle-cut, recursion follows the proposition,
premise selection is bounded by the candidate facts); the memory-resolution
budget of 8,000, alias depth of 64, expensive-edge depth of 8, and the
isolated budgets around the DAG hop checks; the finite-forall instantiation
cap of 128 and per-variable range cap of 32, the disjunction-case cap of 8,
the range-fold unroll cap of 1,024, and a depth of 16 on structural
proposition comparison (enumerations bounded by the query's own inputs,
now charged as deterministic work per instance). Replaced by cycle checks
on the query in progress: the constant-normalization node budget (a
per-walk map of resolved terms), the cell-lookup depth, the resource
composition query depth, and every memory-resolution resolver
(`ResolutionQueryGuard` in `src/kernel/reasoning/memory_resolution.rs`,
with nested queries now going through the memo). Deterministic work over
the profiled examples fell or held on every chunk.

Carved out: the load-equality depth of two (`MEMORY_LOAD_EQUALITY_DEPTH_LIMIT`,
`src/kernel/assumptions.rs`) caps a search, and
`issues/load-equality-prover-in-kernel.md` owns it with the measurements.

## What remains

Every remaining bound under `src/kernel/` caps a search or serves one, so
none is a simple deletion. Counts are examples / mdtests, times fired,
from the slice 7 census of 2026-09-03.

1. **The finite context split**, `FINITE_CONTEXT_SPLIT_LIMIT = 8`
   (`src/kernel/reasoning/order_reasoning.rs`; used by
   `derive_by_finite_context_split` and `proves_by_finite_context_split`
   in `src/kernel/assumptions/proposition_reasoning.rs`, and by the
   derivation checker in `src/kernel/assumptions.rs`). Fired 8 / 840.
   Prover 1 splits the context on a variable with a finite range and
   proves the goal once per value; the cap refuses ranges wider than eight.
   The split is a case analysis the surface should state (a `cases`
   tactic recording one certificate per value); the kernel then checks
   the cases it is given. The census earlier found the split deciding
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
   are enforced in deterministic work units. Deciding whether the kernel
   should observe wall time at all is a separate question from this
   issue's, and the checks are harmless to it.
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

Lessons from slice 7 that a fresh agent should not relearn: build an
in-progress guard with `bool::then(|| Guard)`, never `then_some(Guard)`,
since the eagerly built guard's drop unregisters the outer query on the
cycle path; when a bound is removed and the harness slows, the
replacement was not structural, so census the site rather than tune it;
and nested queries must be memoized once fuel is gone, since the memo
used to refuse anything computed under fuel.

## Intended regression

For every bound replaced, a deterministic scaling regression over several
input sizes showing the replacement's work is bounded by its inputs
(`docs/internals/verification-efficiency.md`); a kernel unit test that
each guard refuses re-entry without unregistering the outer query; and
the fixture harnesses with the contract-fallback census at zero. The
regressions for the landed chunks are in `src/kernel/tests/` and beside
the guards they pin.

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
