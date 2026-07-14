# advance can export a relation to function entry

```c filename=advance_old_state_interface.c
int32 advance_old_state_interface(int32 x, int32 choose_first) {
    int32 y;
    if (choose_first != 0) {
        y = x;
    } else {
        y = x;
    }
    return y;
}
```

```click
verifying "advance_old_state_interface.c";

int32 advance_old_state_interface(int32 x, int32 choose_first) {
    ensures result == old(x) by {
        execute_step();
        advance(statement(1).exit)
        ensuring {
            fact y == old(x);
        }
        by {
            if choose_first != 0 {
                execute_then_step();
                execute_step();
            } else {
                execute_else_step();
                execute_step();
            }
        }
        execute_step();
        simp();
    }
}
```

```expect
pass
```
