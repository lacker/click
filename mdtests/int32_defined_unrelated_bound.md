# `int32_defined` refuses a listed premise that bounds no operand

The rule reads only the listed premises, and each must be a constant `int32`
order or equality fact on an operand of the claimed operation. `c < 5` bounds
neither `a` nor `b`, so the step is refused and names the premise, even though
the other two premises alone would suffice
([`int32_defined_from_bounds.md`](int32_defined_from_bounds.md)).

```c filename=int32_defined_unrelated_bound.c
int sum(int a, int b, int c) {
    return a + b;
}
```

```click
verifying "int32_defined_unrelated_bound.c";

int32 sum(int32 a, int32 b, int32 c) {
    requires a < 100;
    requires b == 1;
    requires c < 5;
    ensures result == a + b;
} by {
    have defined(a + b) by {
        arithmetic_certificate special {
            premise 0: a < 100 => a < 100;
            premise 1: b == 1 => b == 1;
            premise 2: c < 5 => c < 5;
            int32_defined bounds [0, 1, 2] => defined(a + b);
            conclusion 0;
        }
    }
    execute();
    simp();
}
```

```expect
fail: `int32_defined` premise 2 is not a constant int32 order or equality fact on an operand of the claimed operation
```
