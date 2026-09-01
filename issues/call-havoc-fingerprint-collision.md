# Salt call-havoc snapshots so interning cannot attach a narrower write set

Found by the 2026-09-01 kernel audit at cb034b21. The comment at
`src/kernel/primitives/memory_state.rs:483-502` acknowledges this residual
and says "the full claim-scoped salt design is recorded in the issue"; no
such issue existed. This is that issue.

`with_call_memory_havoc` (`memory_state.rs:503-516`) fingerprints the write
set into the call-havoc marker block's size using only the range count, each
range's base block (not its offset), and constant endpoints
(`range.start().as_const()` / `range.end().as_const()`); symbolic endpoints
hash as `None`. The marker block is `call-havoc:{variable}` where the variable
is `variables.next()` (`src/kernel/functions.rs:563`). Memory snapshots are
interned by content in a session-wide arena (`src/kernel/primitives.rs:1261-1342`)
and `record_c_memory_derivation` is first-wins (`primitives.rs:1216-1237`).
One `VerificationSession` spans a whole multi-function verify call
(`src/surface/verification.rs:556-558`) while each execution's variable
counter restarts at 1_000_000 (`src/kernel/primitives/derivations.rs:709`),
so two alpha-aligned executions in one session can mint colliding marker ids.
Two call-havoc snapshots with byte-identical base memory, the same marker id,
and same-shaped ranges of different symbolic widths (`[p, p+n)` vs
`[p, p+m)`) or different symbolic offsets then intern to one node carrying
the first derivation's `mutable_ranges`. `memory_derivations_reach`
(`src/kernel/memory_provenance.rs:714-729`) and `memory_dag_cell_source`
(`:1700-1726`) read those ranges with no fingerprint revalidation, so a load
inside the wider footprint but outside the narrower one is reported unchanged
across a call that could have written it. `src/kernel/mod.rs:88-101`
documents the same hazard across sessions and fixes only that.

## Violated invariant

A `CallHavoc` edge may be crossed only with evidence that the loaded address
is disjoint from every range the call could actually have written. Two
havocs with different write sets must never share one derivation.

## Intended regression

Kernel unit test in `src/kernel/tests/memory_dag_tests.rs`: two executions in
one `VerificationSession` that reach a call-havoc point with content-identical
base memory, the same marker variable, and ranges `[p, p+n)` and `[p, p+m)`
with symbolic `n`, `m`. Assert that the two results are distinct nodes (or
that the second records its own ranges) and that under `n == 0`, `1 <= m`, a
load at `p` after the second havoc is not reported unchanged.

End-to-end mdtest: callee `f(char* p, int n)` with `mutable [p, p+n)`; two
callers identical in parameter names, types, order, and statement prefix,
differing only in which local is passed as the length, one claiming after
`f(p, n)` and the other asserting `p[0]` still equals its stored value after
`f(p, m)` under `n == 0`, `m >= 1`. The second claim must fail.

## Acceptance criteria

- The havoc marker or the interned snapshot carries a fingerprint that
  distinguishes symbolic range endpoints and base offsets (for example the
  canonical form of each range term, or a claim-scoped salt as the comment
  proposes), so semantically different write sets never intern to one node.
- The DAG crossing revalidates the recorded ranges against the querying
  execution's ranges, or the design guarantees that revalidation is
  unnecessary and a test pins the guarantee.
- The comment at `memory_state.rs:483-502` points at this file or is removed
  when the residual is closed.
- The kernel test and mdtest above; `scripts/check.sh` passes.
