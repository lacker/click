# execute until requires a determined branch

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
fail: could not prove that the next C `if` condition `flag` is one exact truth value
```
