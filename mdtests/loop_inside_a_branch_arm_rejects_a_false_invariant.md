# a `branch` arm's loop still owes its invariant bundle

The arm's path condition is a premise of the loop's obligations, not a licence
to skip them. `invariant i <= 0` is false after the body increments `i`, so the
back-edge bundle stays open exactly as it would for a top-level loop.

```c filename=loop_inside_a_branch_arm_rejects_a_false_invariant.c
int32 count_up(int32 n) {
    int32 i;
    i = 0;
    if (n > 0) {
        while (i < n) {
            i = i + 1;
        }
    }
    return i;
}
```

```click
verifying "loop_inside_a_branch_arm_rejects_a_false_invariant.c";

int32 count_up(int32 n) {
    ensures result >= 0;
} by {
    step();
    step();
    branch {
        ensuring {
            fact i >= 0;
        }
        then {
            loop {
                decreases n - i;
                invariant i <= 0;
            }
        }
        else {}
    }
    step();
    simp();
}
```

```expect
fail: closure body did not prove every invariant obligation
```
