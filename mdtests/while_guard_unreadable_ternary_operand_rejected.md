# An unreadable operand inside a guard's `?:` is the same hole

A conditional expression selects its arm from a value, so an arm that cannot be
evaluated is exactly as undecided as an unevaluable `&&` operand. The exit here
is `a == 0` or `a != 0 && p[0] == 0`; keeping only the first would prove
`result == 0` for a function that returns a nonzero `a` whenever `p[0] == 0`.

```c filename=while_guard_unreadable_ternary_operand_rejected.c
int32 uternary(int32 a, int32 *p) {
    while (a != 0 ? p[0] != 0 : 0) {
        a = 0;
    }
    return a;
}
```

```click
verifying "while_guard_unreadable_ternary_operand_rejected.c";

int32 uternary(int32 a, int32* p) {
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
