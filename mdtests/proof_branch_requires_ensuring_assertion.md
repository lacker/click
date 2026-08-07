# Branch requires every arm to establish its ensuring assertions

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
        branch {
            ensuring {
                fact y == x;
            }
            then {
                step();
            }
            else {
                step();
            }
        }
        step();
        simp();
    }
}
```

```expect
fail: in else arm of C `if` at statement(1):
`advance_missing_fact.ensures_0` tactic 1: `branch ensuring` did not establish fact
```
