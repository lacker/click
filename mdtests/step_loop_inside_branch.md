# execute a verified loop inside a selected branch

This checks that execution proofs retain source-region identity after entering a
C branch. The then arm advances across a verified loop and records its labeled
exit snapshot; the else arm executes an ordinary assignment. Both continue at
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

    for statement(0) {
        assert flag != 0 by auto;
    }

    for statement(1) {
        assert i == 1 by auto;
    }

    ensures result == 1
        and at(statement(1).exit, i) == 1
        and at(statement(4).entry, i) == 1;
} by {
    step();
    loop as count {
        invariant i == 1;
    }
    have at(count.exit, i) == 1 by simp;
    step();
    simp();
}
```

```expect
pass
```
