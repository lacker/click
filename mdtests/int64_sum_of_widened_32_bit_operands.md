# An `int64` sum of widened 32-bit operands is defined by their widths

A `long` addition of a value widened from `unsigned int` and one widened from
`int` cannot overflow: the first lies in `[0, 2^32)`, the second in
`[-2^31, 2^31)`, so every sum lies far inside `int64`. The same holds for
their difference. The signed-overflow condition for 64-bit addition and
subtraction is therefore decided false from the operands' widening
constructors alone, with no bounds in the context.

Before this rule the kernel split such an addition into a normal path and a
signed-overflow path, and `step()` reported `undefined behavior: signed
overflow` even under `requires` bounds that excluded it.

`widened_sum` and `widened_difference` have no bounds at all. `bounded_sum`
keeps the original report's bounds, which the width argument makes
unnecessary. `mixed_load` widens a caller's `int` read through a pointer, the
pattern a tagged-word demo needed.

The claim under test is that execution reaches `return` with no undefined
behavior, so each postcondition only names the result. Relating the widened
sum's value to `to_integer(t) + to_integer(x)` is a separate question about
the Integer bridge through a widening, which this file does not cover.

Only the width range of a widening conversion is used. An `int64` operand
with no known range still needs evidence
([`int64_sum_without_bounds_overflows.md`](int64_sum_without_bounds_overflows.md)),
and `int64` bounds stated as `requires` are covered in
[`int64_sum_with_bounds.md`](int64_sum_with_bounds.md).

```c filename=int64_sum_of_widened_32_bit_operands.c
long widened_sum(unsigned t, int x) {
    long w = t;
    return w + x;
}

long widened_difference(unsigned t, int x) {
    long w = t;
    return w - x;
}

long bounded_sum(unsigned t, int x) {
    long w = t;
    return w + x;
}

long mixed_load(unsigned int tag, int *p) {
    long r = (long)tag + *p;
    return r;
}
```

```click
verifying "int64_sum_of_widened_32_bit_operands.c";

int64 widened_sum(uint32 t, int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}

int64 widened_difference(uint32 t, int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}

int64 bounded_sum(uint32 t, int32 x) {
    requires t <= 1000;
    requires 0 <= x;
    requires x <= 1000;
    ensures result == result;
} by {
    execute();
    simp();
}

int64 mixed_load(uint32 tag, int32* p) {
    requires tag <= 1000;
    owns p[0..1];
    requires 0 <= p[0];
    requires p[0] <= 1000;
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
pass
```
