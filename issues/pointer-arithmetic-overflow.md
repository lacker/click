# Model out-of-object pointer formation as undefined behavior

Split from the pointer-offset-wrap issue on 2026-09-01 when the decision
procedure half of it landed.

`pointer + int` always yields a `Value` path
(`src/kernel/eval/operators.rs:131-151`), and `CUndefinedBehavior`
(`src/kernel/primitives.rs:742-748`) has no pointer-arithmetic variant, so
forming `data + INT_MAX + 1` (undefined in ISO C: the result is outside the
object and not one past its end) is silently accepted as a value with an
exact i64 offset. The kernel no longer decides such pointers equal to others
by a wrapped index comparison (`rebuilt_offset_is_exact` in
`src/kernel/assumptions/condition_reasoning/order_paths.rs`), but a function
that forms the pointer is still certified free of undefined behavior.

## Violated invariant

Pointer formation outside the pointed-to object, other than one past its
end, is undefined behavior and must produce a UB outcome or an obligation,
not a value.

## Intended regression

`mdtests/c_pointer_equality_rejects_wrapped_index_sum.md` forms
`data + i + j` with `i == INT_MAX`, `j == 1`. Today it fails only because
`p == q` is undecided; after this issue it must fail at the pointer formation
with an undefined-behavior diagnostic, and a positive mdtest must show that
`data + n` under `views data[0..n]` (one past the end) is still accepted.

## Acceptance criteria

- `offset_by_elements` and the byte-offset path emit an obligation that the
  resulting offset lies within `[0, size]` of the pointer's block when the
  block extent is known, or a signed-overflow obligation on the element index
  otherwise; violating paths produce a `CUndefinedBehavior` outcome.
- Kernel unit tests for the wrapping `int32` and `uint8` cases; the mdtest
  above expects the UB diagnostic; the one-past-the-end mdtest passes.
- `scripts/check.sh` passes.
