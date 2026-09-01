# Extend arithmetic reasoning past affine terms

Found by the 2026-09-01 kernel audit at cb034b21.

- `collect_affine_bitvector_terms` (`src/kernel/assumptions.rs:2912-2942`)
  handles only `Constant`, `Add`, `Subtract`, and opaque atoms; `Multiply` is
  an atom, so `affine_bitvector_difference_constant` and its users in range
  containment and disjointness cannot relate `i * stride` or
  `row * width + col` to constant offsets. Strided and two-dimensional
  access patterns cannot be shown in range or disjoint.
- `signed_interval_uncached`
  (`src/kernel/assumptions/condition_reasoning/overflow_intervals.rs:333-342`)
  returns early for `Bitvector32Term::Add` by summing operand intervals and
  never consults order facts (`exact_signed_order_bounds`,
  `overflow_intervals.rs:346`) recorded on the `Add` term itself (only direct
  equalities are checked first, at `:329-332`), so a fact such as
  `(i + 1) < n` contributes nothing to the interval of `i + 1` and
  overflow discharge for nested sums degrades.
- The explicit `arithmetic()` closer (`src/kernel/proof/fact_reasoning.rs:89-99`,
  `:245-255`, goal rejection at `:321`) models only affine combinations and
  reports `Unsupported` for any goal involving divide, remainder, shifts,
  bitwise operators, `If`, or `RangeFold`.

## Violated invariant

The deterministic reasoning rules should decide the index arithmetic real C
uses: multiplication by a constant or by a bounded variable, remainder and
shift by constants, and bounds recorded on compound terms.

## Intended regression

Kernel unit tests: `row * width + col < width * height` from `0 <= row <
height`, `0 <= col < width`, and no-overflow facts; disjointness of
`a + i * 4` and `a + j * 4` under `i != j` with symbolic `i, j` as int32
elements in a byte-addressed buffer; interval of `i + 1` from a recorded
`(i + 1) < n`; the `arithmetic()` closer proving `(x & 0xFF) <= 255` and
`(x >> 1) <= x` for nonnegative `x`. An mdtest verifying a row-major
2-D fill loop with in-bounds obligations.

## Acceptance criteria

- `collect_affine_bitvector_terms` gains a `Multiply` arm with a constant
  operand (mirroring `collect_signed_affine_terms` in
  `src/kernel/proof/fact_reasoning.rs:52-70`) so multiplication by a constant
  is affine, and multiplication of two bounded terms produces an interval
  fact.
- Interval reconstruction consults facts on compound terms before
  decomposing them.
- The arithmetic closer supports constant shifts, remainder by a constant,
  and bitwise-and with a constant mask, with proofs that each rule is valid
  over Z/2^32.
- The tests above pass; `scripts/check.sh` passes.
