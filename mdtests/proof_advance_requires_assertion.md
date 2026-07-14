# advance requires every case to establish its assertions

```c filename=advance_missing_fact.c
int32 advance_missing_fact(int32 x) {
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
verifying "advance_missing_fact.c";

int32 advance_missing_fact(int32 x) {
    ensures result == result by {
        execute_step();
        advance(statement(1).exit)
        ensuring {
            fact y == x;
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
fail: in else branch of proof `if x >= 0`:
`advance_missing_fact.ensures_0` proof step 1: `advance` did not establish fact
```
