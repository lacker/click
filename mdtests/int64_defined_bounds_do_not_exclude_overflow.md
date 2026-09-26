# `int64_defined` refuses bounds that leave room for overflow

The listed bound `a < 100` limits `a` from above only, and nothing bounds `b`,
so `a + b` ranges over far more than `int64`. The `int64_defined` rule
recomputes that range from the listed premises and the operands' widths and
refuses, naming the range it found and what would fix it. The same step
succeeds once each operand is bounded:
[`int64_defined_from_bounds.md`](int64_defined_from_bounds.md).

```c filename=int64_defined_bounds_do_not_exclude_overflow.c
long sum(long a, long b) {
    return a + b;
}
```

```click
verifying "int64_defined_bounds_do_not_exclude_overflow.c";

int64 sum(int64 a, int64 b) {
    requires a < 100;
    ensures result == a + b;
} by {
    have defined(a + b) by {
        arithmetic_certificate special {
            premise 0: a < 100 => a < 100;
            int64_defined bounds [0] => defined(a + b);
            conclusion 0;
        }
    }
    execute();
    simp();
}
```

```expect
fail: the listed bounds and the operands' widths put the exact result in [-18446744073709551616, 9223372036854775906], which leaves int64
```
