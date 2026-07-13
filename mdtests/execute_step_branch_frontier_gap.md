# execute step branch frontier gap

This records the missing multi-frontier execution model. Each branch proves a
different fact about `y`, but both prove the bound needed to execute the
possibly overflowing increment. The intended proof pauses after the `if`,
derives that bound at every frontier, and then continues one statement at a
time.

Currently `execute_step()` only accepts straight-line statements, so it cannot
cross the `if`. Once branch stepping exists, the proof state will need to retain
one path-indexed pure/resource context per resulting execution frontier.

```c filename=increment_nonnegative.c
int32 increment_nonnegative(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
```

```click
verifying "increment_nonnegative.c";

int32 increment_nonnegative(int32 x) {
    requires x < 2147483647;

    ensures result > 0 by {
        execute_step();
        execute_step();
        have y < 2147483647 by {
            simp();
        }
        execute_step();
        execute_step();
        simp();
    }
}
```

```expect
fail: next statement is not a supported straight-line statement
```
