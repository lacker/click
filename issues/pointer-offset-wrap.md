# Decide pointer-offset equality in the offset model, not modulo 2^32

Found by the 2026-09-01 kernel audit at cb034b21. Reproduced with
`click verify` (exit 0) for both `int32` and `uint8` element arrays.

`PointerOffsetTerm` semantics are exact i64: `as_const` uses checked i64
arithmetic on `(v as i32 as i64) * width`
(`src/kernel/primitives/term_operations.rs:440-451`) and
`ConditionTerm::pointer_offset_equal` folds constants by i64 equality
(`:577-585`). `pointer_equality_condition` (`src/kernel/eval/operators.rs:1191`)
emits `PointerOffsetEqual` for same-block `p == q`, and `decide_inner`
(`src/kernel/assumptions/condition_reasoning/decision.rs:99-108`) routes it to
`decide_from_order_facts`
(`src/kernel/assumptions/condition_reasoning/order_paths.rs:44-73`). Its
fallback rebuilds both offsets through `int32_element_index_from_offset` and
`byte_offset_from_pointer_offset` (`src/kernel/reasoning/path_facts.rs:210-235`,
`:267-290`) as wrapping 32-bit index terms and returns
`self.decide(equal(li, ri))` in both directions. Mod-2^32 index equality does
not imply i64 offset equality when the index sum wraps, so the `Some(true)`
direction asserts an offset equality that is false in the kernel's own model.
The `Some(false)` direction stays sound.

Separately, `pointer + int` always yields a `Value` path
(`operators.rs:131-151`) and `CUndefinedBehavior`
(`src/kernel/primitives.rs:742-748`) has no pointer-arithmetic variant, so
forming `data + INT_MAX + 1` (undefined in ISO C) is silently accepted. That
is what lets the regression below certify a function as UB-free.

## Violated invariant

A `Some(true)` decision for `PointerOffsetEqual` must be valid under the exact
offset semantics the rest of the kernel uses. Pointer formation outside the
object (plus one past the end) is undefined behavior and must produce a UB
outcome or an obligation, not a value.

## Intended regression

```c
int32 ptr_cmp(int32 data[], int32 i, int32 j, int32 k) {
    int32* p; int32* q; p = data + i + j; q = data + k;
    if (p == q) { return 1; } return 0;
}
```

```click
verifying "ptr_cmp.c";
int32 ptr_cmp(int32 data[], int32 i, int32 j, int32 k) {
    requires i == 2147483647; requires j == 1; requires k == -2147483647 - 1;
    ensures result == 1;
} by { execute(); simp(); }
```

Today this exits 0; `ensures result == 0` is rejected because the kernel
positively believes `p == q`; the non-wrapping control `i == 5, j == 1,
k == 7` with `ensures result == 1` is correctly rejected; the `uint8 data[]`
twin also verifies through the byte-offset path. After the fix the wrapping
sidecar must fail, either because `p == q` is left undecided or because
`data + i + j` produces a UB path that the proof must discharge and cannot.

## Acceptance criteria

- `decide_from_order_facts` returns `Some(true)` for `PointerOffsetEqual` only
  with a proven non-wrapping index or byte sum on both sides (in-range facts
  or an explicit no-overflow fact), or the fallback is restricted to the
  `Some(false)` direction.
- Pointer formation in `offset_by_elements` and the byte-offset path emits a
  signed-overflow or out-of-object obligation, or a documented decision
  records why the model accepts it and the decision procedure is fixed alone.
- Kernel unit tests for the wrapping `int32` and `uint8` cases; negative
  mdtests for both sidecars; `scripts/check.sh` passes.
