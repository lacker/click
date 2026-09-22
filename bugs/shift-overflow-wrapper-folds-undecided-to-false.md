# The shift-overflow wrapper turns the out-of-range refusal into 'safe'

P1. A deciding rule requires the evidence its conclusion depends on; here
the element of evidence (a bounded shift count) is absent, and the wrapper
invents a safe answer.

## What was found

`signed_shift_left_overflows_const`
(`src/kernel/primitives/term_operations.rs:56`) answers `None` for a
concrete shift count outside `0..32` — the honest
"not decided, apply the UB gate" answer the interval decider
consistently produces. But the deciding constructor arm at
`term_operations.rs:2211`
(`(Some(left), Some(right)) => Constant(signed_shift_left_overflows_const(left, right).unwrap_or(false))`)
turns that refusal into `Constant(false)` — "the shift is overflow-free" —
for exactly the shapes where C leaves the operation undefined
(shift count >= width). Machine witness:
`hunt_investigation_out_of_range_shift_count_is_undecided_by_the_helper`
(`src/kernel/primitives/term_operations.rs` investigation module) records
the helper's `None` and the wrapper's `unwrap_or(false)` completion.

The eval path escapes only because its count-range gate fires first
(`src/kernel/eval/operators.rs`, `apply_c_int64_with_valid_shift_count`
and the `0..width` gate). The proof routes do not share that gate:
`signed_arithmetic_planner.rs` spends
`Bitvector32SignedShiftLeftOverflows` conditions (lines around 800, 1873,
2475) and `decision.rs` re-derives the condition through the same fold — a
proof goal "no signed shift overflow" with an out-of-range concrete count
is discharged by the folded `false`. Related same-shape gap: the 64-bit
count path wraps a `long long` count through a 32-bit constructor before
the range decision (`promote_c_shift_count` returning the raw 64-bit
carrier into `int64_from_32`/`uint64_from_32`, `src/kernel/eval/operators.rs:2608`),
which answers the count's low 32 bits — a count of `2^32+2` behaves as
shift 2.

## Intended regression

(a) The wrapper folds `(Constant(1), Constant(40))` to an explicit refusal
(or to the UB-reporting condition) instead of `Constant(false)`; (b) the
eval shift path splits on a 64-bit symbolic count whose 32-bit low word is
small and labels the operation UB-or-safety-checked at the exact value.

## Acceptance

- [ ] The constructor refuses (stays undecided or asserts the UB) for
      out-of-range counts, with the regression green.
- [ ] `scripts/check.sh` green.
