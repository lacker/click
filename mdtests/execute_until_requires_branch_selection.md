# execute until requires explicit branch selection

```c filename=execute_until_unresolved_branch.c
int32 execute_until_unresolved_branch(int32 flag) {
    if (flag) {
        flag = 1;
    } else {
        flag = 0;
    }
    return flag;
}
```

```click
verifying "execute_until_unresolved_branch.c";

int32 execute_until_unresolved_branch(int32 flag) {
    ensures result >= 0 by {
        execute_until(statement(3));
        execute_rest();
        simp();
    }
}
```

```expect
fail: next statement is an `if`; use `execute_then_step()` or `execute_else_step()`
```
