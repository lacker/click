# Join branches that differ in heap deallocation

Found by the 2026-09-01 kernel audit at cb034b21.

When one arm of an interface `branch ensuring` join frees heap memory,
`checked_interface_effect_facts` rejects the join outright (a plain
exhaustive `branch` already fails earlier, at `execution.rs:780`, because the
arm states differ): `src/kernel/proof/execution.rs:1198-1202`
(`Proposition::CHeapAllocationFreed { .. } => return Err("an interface join
over conditional heap deallocation is not yet supported")`). Freeing in one
branch and not the other (error-path cleanup, conditional release) is a
common real-C pattern, and there is no interface-specific fallback.

## Violated invariant

A branch join should be able to summarize arms whose heap lifetime states
differ, exporting the conditional allocation state (or a resource whose
guard records which arm ran) instead of refusing.

## Intended regression

Mdtest: `if (err) { free(p); r = -1; } else { r = 0; } ... return r;` with
both arms continuing to the join, joined with `branch ensuring` that exports
`r == -1 implies` the allocation is gone and `r == 0 implies allocation(p,
n)` still held, plus a function-level `ensures result == -1 implies ...`
over the retained paths. A second with a guarded resource
`maybe_alloc(p, n, alive)` exported at the join.

## Acceptance criteria

- The interface join accepts arms with differing `CHeapAllocationFreed`
  facts and derives a conditional lifetime successor checked by the kernel.
- The exported state is a guarded resource or a disjunction the continuation
  can case-split on; both arms remain mandatory.
- The tests above pass; `scripts/check.sh` passes.

Related: [double-execution.md](double-execution.md) owns the join evidence
design this extends.
