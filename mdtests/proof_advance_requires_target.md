# advance requires every case to reach its target

```c filename=advance_wrong_target.c
int32 advance_wrong_target(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    return y;
}
```

```click
verifying "advance_wrong_target.c";

int32 advance_wrong_target(int32 x) {
    ensures result == result by {
        execute_step();
        advance(statement(2).exit)
        ensuring {
            fact y >= 0;
        }
        by {
            if x >= 0 {
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
fail: `advance` branch did not reach `statement(2).exit`
```
