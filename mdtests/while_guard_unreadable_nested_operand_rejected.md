# A nested `&&` hides the unreadable operand no better

The unevaluable read sits in the innermost conjunct here, so the guard's value
is undecided on every path that reaches it. The exit assumption must stay the
negation of the whole guard.

```c filename=while_guard_unreadable_nested_operand_rejected.c
int32 unested(int32 a, int32 b, int32 *p) {
    while (a != 0 && (b != 0 && p[0] != 0)) {
        a = 0;
    }
    return a;
}
```

```click
verifying "while_guard_unreadable_nested_operand_rejected.c";

int32 unested(int32 a, int32 b, int32* p) {
    requires a >= 0;
    requires a <= 10;
    requires b == 1;
    ensures result == 0;
} by {
    loop {
        invariant a >= 0;
        invariant a <= 10;
        invariant b == 1;
    }
    step();
    simp();
}
```

```expect
fail: the loop condition could not be evaluated
```
