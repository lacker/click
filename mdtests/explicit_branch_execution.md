# explicit branch execution

This checks frontier-local execution of a C `if`. The `branch` tactic reads the
condition from the source, enters both feasible arms, and requires each arm's
proof to stop at the shared continuation.

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
        step();
        branch {
            ensuring {
                fact y >= 0;
                fact y < 2147483647;
            }
            then {
                step();
            }
            else {
                step();
            }
        }
        have y < 2147483647 by simp;
        step();
        step();
        simp();
    }
}
```

```expect
pass
```
