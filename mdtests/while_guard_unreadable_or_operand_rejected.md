# An unreadable `||` operand leaves the guard undecided too

Leaving this loop needs `a != 0 && p[0] == 0`, and `p[0]` is a read this
function has no authority for. Dropping that operand removes the loop's only
exit instead of inventing a false one, so this shape does not prove a false
`ensures` the way the `&&` guards do — but the guard is just as undecided, and
Click must say so rather than report a downstream tactic failure.

```c filename=while_guard_unreadable_or_operand_rejected.c
int32 uor(int32 a, int32 *p) {
    while (a == 0 || p[0] != 0) {
        a = 1;
    }
    return a;
}
```

```click
verifying "while_guard_unreadable_or_operand_rejected.c";

int32 uor(int32 a, int32* p) {
    requires a >= 0;
    requires a <= 10;
    ensures result == 7;
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
