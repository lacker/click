# A `for` guard lowers to the same loop and keeps the same duty

`for` is lowered to a `while` whose update clause is part of the continue
transfer, so an unevaluable guard operand has to be refused there too. Dropping
`p[0] != 0` here leaves `i == 0` as the exit assumption and proves
`result == 0`, although the loop never runs when `p[0] == 0` and the function
then returns the nonzero `a` it started `i` from.

```c filename=for_guard_unreadable_operand_rejected.c
int32 ufor(int32 a, int32 *p) {
    int32 i;
    for (i = a; i != 0 && p[0] != 0; i = i - 1) {
        i = 1;
    }
    return i;
}
```

```click
verifying "for_guard_unreadable_operand_rejected.c";

int32 ufor(int32 a, int32* p) {
    requires a >= 0;
    requires a <= 10;
    ensures result == 0;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= 10;
    }
    step();
    simp();
}
```

```expect
fail: the loop condition could not be evaluated
```
