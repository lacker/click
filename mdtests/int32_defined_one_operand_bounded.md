# `int32_defined` refuses a sum with only one operand bounded

`0 <= a` and `a < 100` bound `a` on both sides, but nothing bounds `b`, so
`b` keeps its whole `int32` range and `a + b` can leave `int32` at the top.
An unconverted `int32` term has no narrower root constructor that would give
it a smaller range, so the rule refuses and reports the range it found. The
bounded form is [`int32_defined_from_bounds.md`](int32_defined_from_bounds.md).

```c filename=int32_defined_one_operand_bounded.c
int sum(int a, int b) {
    return a + b;
}
```

```click
verifying "int32_defined_one_operand_bounded.c";

int32 sum(int32 a, int32 b) {
    requires 0 <= a;
    requires a < 100;
    ensures result == a + b;
} by {
    have defined(a + b) by {
        arithmetic_certificate special {
            premise 0: 0 <= a => 0 <= a;
            premise 1: a < 100 => a < 100;
            int32_defined bounds [0, 1] => defined(a + b);
            conclusion 0;
        }
    }
    execute();
    simp();
}
```

```expect
fail: put the exact result in [-2147483648, 2147483746], which leaves int32
```
