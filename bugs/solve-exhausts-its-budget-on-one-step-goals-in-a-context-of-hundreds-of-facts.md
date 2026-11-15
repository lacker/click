# solve exhausts its budget on one-step goals in a context of hundreds of facts

Soundness: not soundness. A true goal is not proved and the failure is a
budget exhaustion; nothing false is accepted.

In a proof state holding several hundred recorded facts, a bare `have` whose
goal follows from one or two facts already in the context exhausts the smart
budget (2,000,000 units). The same goal closes at once when those facts are
listed with `solve() using { ... }`. The cost is in `solve` spelling premises
across recorded states, not in the arithmetic.

Invariant: smart search is bounded by the selected goal and the relevant
state, not by the size of the surrounding context
(`docs/internals/verification-efficiency.md`); a single prompt miss is
acceptable, a budget exhaustion on a one-step goal is not.

Related: `bugs/solve-exhausts-its-budget-spelling-premises-of-an-inclusive-range-loop.md`
reports the same phase on a different shape.

## Reproduction

`design/adler32/project/adler2/general-compute.click` on master. Each site
below is a `have ... by solve() using { ... }`. Deleting the `by solve()
using { ... }` so the `have` is bare makes the claim fail with
`verification budget exhausted ... after 2000001 units`. Observed while
porting the proof (clicklang/click#2610), with the assembled sidecar:

1. Remainder-chunk loop back edge, about 369 recorded premises:

   ```click
   have loop(2).iter.len() <= remainder_chunk_len / 4u64 by solve() using {
       to_integer(loop(2).iter.len()) + (iterations + 1) == to_integer(remainder_chunk_len / 4u64);
       0 <= iterations;
   };
   ```

2. Scalar tail loop head, about 468 premises:

   ```click
   have to_integer(((__rust_mir_138_remaining as u32) as i32) - 1) <= to_integer(((remainder_len as u32) as i32))
   ```

   with premises `0 < ((__rust_mir_138_remaining as u32) as i32)` and
   `((__rust_mir_138_remaining as u32) as i32) <= ((remainder_len as u32) as i32)`.

3. Scalar tail loop before `a += byte`, about 502 premises:

   ```click
   have a <= 4294967295u32 - __rust_mir_144 by solve() using {
       to_integer(a) + to_integer(__rust_mir_144) <= 4294967295;
   };
   ```

   The premise is the first `ensures` of the lemma applied on the line before.

A fourth site (remainder lane sum, about 423 premises) failed differently:
`could not lower integer certificate premise / Integer lowering exceeded the
numeric operation or active verification work budget`, after search selected
an unrelated range premise. It is written as
`apply(integer::uint32_add_to_integer(L, R)) using { ... }`.

Run the nightly test
`adler2_helpers::charon_adler2_general_compute_proves_original_body` after
making one `have` bare to reproduce; use `CLICK_TIMINGS=1` for attribution.

## Acceptance criteria

- A deterministic scaling regression in `src/scaling_tests/`: a one-step
  linear goal whose two premises are in the context, with N unrelated
  recorded facts and states for several N; `solve` work does not grow
  with N beyond indexing factors.
- The three bare `have`s above close within budget, or miss promptly with a
  bounded message that names `solve() using`.
- The `using` lists at those sites in `general-compute.click` can be removed.
