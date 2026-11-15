# execute a verified loop inside a selected branch

This checks that execution proofs retain source-region identity after entering a
C branch. The then arm advances across a verified loop and records its labeled
exit state; the else arm executes an ordinary assignment. Both continue at
the common return.

```c filename=step_loop_inside_branch.c
int32 branch_count_to_one(int32 flag, int32 i) {
    if (flag) {
        while (i < 1) {
            i = i + 1;
        }
    } else {
        i = 1;
    }
    return i;
}
```

```click
verifying "step_loop_inside_branch.c";

int32 branch_count_to_one(int32 flag, int32 i) {
    requires i == 1;
    requires flag != 0;

    ensures result == 1
        and at(region(1).exit, i) == 1
        and at(region(4).entry, i) == 1;
} by {
    have flag != 0 by {
        known();
    }
    step();
    have i == 1 by {
        known();
    }
    loop as count {
        decreases 0;
        invariant i == 1;
    }
    have at(count.exit, i) == 1;
    step();
    solve();
}
```

```expect
pass
```
