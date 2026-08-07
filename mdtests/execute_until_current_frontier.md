# execute until from the current frontier

`execute_until` composes with earlier execution steps and selected branches.
It records the same statement snapshots as repeated
`step` calls.

```c filename=execute_until_after_step.c
int32 execute_until_after_step(int32 x) {
    int32 y;
    y = x;
    y = 5;
    return y;
}
```

```c filename=execute_until_selected_branch.c
int32 execute_until_selected_branch(int32 flag) {
    int32 y;
    if (flag) {
        y = 1;
        y = 2;
    } else {
        y = 0;
    }
    return y;
}
```

```c filename=execute_until_after_advance.c
int32 execute_until_after_advance(int32 flag) {
    int32 y;
    if (flag) {
        y = 1;
    } else {
        y = 0;
    }
    y = 2;
    y = 3;
    return y;
}
```

```click
verifying "execute_until_after_step.c";
verifying "execute_until_selected_branch.c";
verifying "execute_until_after_advance.c";

int32 execute_until_after_step(int32 x) {
    requires x == 4;

    ensures result == 5
        and at(statement(2).exit, y) == 5
        and at(statement(3).entry, y) == 5 by {
        step();
        execute_until(statement(3));
        step();
        simp();
    }
}

int32 execute_until_selected_branch(int32 flag) {
    requires flag != 0;

    ensures result == 2
        and at(statement(3).entry, y) == 1
        and at(statement(5).entry, y) == 2 by {
        step();
        step();
        execute_until(statement(3));
        execute_until(statement(5));
        step();
        simp();
    }
}

int32 execute_until_after_advance(int32 flag) {
    ensures result == 3 by {
        step();
        branch {
            ensuring {
                fact y >= 0;
            }
            then {
                step();
            }
            else {
                step();
            }
        }
        execute_until(statement(6));
        step();
        simp();
    }
}
```

```expect
pass
```
