# reach requires every case to establish its assertions

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
        step();
        reach(statement(1).exit)
        ensuring {
            fact y == x;
        }
        by {
            if x >= 0 {
                step();
                step();
            } else {
                step();
                step();
            }
        }
        step();
        simp();
    }
}
```

```expect
fail: in else branch of proof `if x >= 0`:
`advance_missing_fact.ensures_0` tactic 1: `reach` did not establish fact
```
