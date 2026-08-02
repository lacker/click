# execute until rejects a target on a skipped branch

```c filename=execute_until_skipped_branch.c
int32 execute_until_skipped_branch(int32 flag) {
    if (flag) {
        flag = 1;
    } else {
        flag = 0;
    }
    return flag;
}
```

```click
verifying "execute_until_skipped_branch.c";

int32 execute_until_skipped_branch(int32 flag) {
    requires flag != 0;

    ensures result == 1 by {
        step();
        execute_until(statement(2));
        execute();
        simp();
    }
}
```

```expect
fail: `execute_until(statement(2))` target is not reachable from the current execution path
```
