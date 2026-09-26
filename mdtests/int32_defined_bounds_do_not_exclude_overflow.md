# `int32_defined` refuses bounds that leave room for overflow

Both operands are bounded, but only from below: `0 <= a` and `0 <= b` put
`a + b` in `[0, 2 * INT32_MAX]`, which leaves `int32`. The `int32_defined`
rule recomputes that range from the listed premises and the operands' widths
and refuses, naming the range it found and what would fix it. The same step
succeeds once the bounds keep the result in range:
[`int32_defined_from_bounds.md`](int32_defined_from_bounds.md).

```c filename=int32_defined_bounds_do_not_exclude_overflow.c
int sum(int a, int b) {
    return a + b;
}
```

```click
verifying "int32_defined_bounds_do_not_exclude_overflow.c";

int32 sum(int32 a, int32 b) {
    requires 0 <= a;
    requires 0 <= b;
    ensures result == a + b;
} by {
    have defined(a + b) by {
        arithmetic_certificate special {
            premise 0: 0 <= a => 0 <= a;
            premise 1: 0 <= b => 0 <= b;
            int32_defined bounds [0, 1] => defined(a + b);
            conclusion 0;
        }
    }
    execute();
    simp();
}
```

```expect
fail: the listed bounds and the operands' widths put the exact result in [0, 4294967294], which leaves int32 [-2147483648, 2147483647]
```
