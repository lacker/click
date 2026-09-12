# A `while` guard operand the function cannot read must not be dropped

The second conjunct of this guard reads through `p`, which the function does
not own or view. That operand is unevaluable, so the guard's truth value is
undecided whenever `a != 0`: the loop may run or may exit with `a` nonzero.

Dropping the unevaluable operand would leave `!(a != 0)` as the only exit
assumption and would prove `result == 0`, which is false when `p[0] == 0` and
`a` is nonzero. Click must refuse instead.

```c filename=while_guard_unreadable_operand_rejected.c
int32 uprec(int32 a, int32 *p) {
    while (a != 0 && p[0] != 0) {
        a = 0;
    }
    return a;
}
```

```click
verifying "while_guard_unreadable_operand_rejected.c";

int32 uprec(int32 a, int32* p) {
    requires a >= 0;
    requires a <= 10;
    ensures result == 0;
} by {
    loop {
        invariant a >= 0;
        invariant a <= 10;
    }
    step();
    simp();
}
```

```expect
fail: the loop condition could not be evaluated
```
