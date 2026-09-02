# Evaluate pointer relational comparison and pointer subtraction

Found by the 2026-09-01 kernel audit at cb034b21.

`CExpression::LessThan`, `LessEqual`, `GreaterThan`, `GreaterEqual`, and
`Subtract` all route through `evaluate_c_int32_binary_paths`
(`src/kernel/eval/expression.rs:169-256`), which calls
`promote_c_int32_path_value` on each operand; that returns `None` for
`CValue::Pointer` (`src/kernel/eval/expression.rs:37-50`), and the call site
at `operators.rs:1228-1238` turns the `None` into a
`CRuntimeError::TypeMismatch` outcome for any pointer operand. Only `Add` has a
pointer-aware path (`operators.rs:131-171`) and only `==`/`!=` compare
pointers (`operators.rs:1191`, with integer mixing restricted to the constant
0). The frontend lowers `p < end` and `end - start` straight to the int32
operators. The cursor idiom `while (p < end)` and length computation
`end - start` are therefore unverifiable.

## Violated invariant

Click should evaluate pointer relational comparison and pointer subtraction
with C's semantics: both operands must point into (or one past) the same
object, comparison orders by offset, subtraction yields an element count, and
violations are undefined behavior.

## Intended regression

Mdtests with unchanged C: `while (p < end) { *p = 0; p = p + 1; }` with a
postcondition over the range; `return (int32)(end - start);` (or the
un-cast form until casts land) with `ensures result == n` under
`end == start + n`; `p - 1` used to step back. Negative mdtests: comparing
pointers into different blocks is rejected as undefined behavior; subtracting
pointers into different blocks likewise.

## Acceptance criteria

- Subtraction gains a value-typed `apply_c_subtract` dispatcher (mirroring
  `apply_c_add` at `operators.rs:108`, with `apply_c_int32_subtract` at
  `:232` as its int32 arm) and the four ordered comparisons gain pointer
  arms: same-block obligation, offset arithmetic in the
  `PointerOffsetTerm` model, and a UB path for cross-block operands.
- `ConditionTerm` has pointer-order forms (or lowers to offset comparison
  under a same-block fact) that the decision procedures can decide.
- Loop invariants can state `p <= end` and `p == start + i`.
- `scripts/check.sh` passes.

Related: `rebuilt_offset_is_exact` (the wrapped-index equality fix, landed 2026-09-01) fixes the
offset-equality decision these forms will rely on;
`havoc_loop_modified_locals` (pointer locals are havoced since 2026-09-01) must land for
the cursor idiom to be sound.
