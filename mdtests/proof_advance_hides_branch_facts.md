# advance hides branch-specific facts

The continuation may use only the declared `ensuring` interface. Although the
two concrete branches assign `0` and `1`, the exported lower bound alone does
not prove the omitted upper bound.

```c filename=advance_hidden_branch_fact.c
int32 advance_hidden_branch_fact(int32 x) {
    int32 y;
    if (x >= 0) {
        y = 0;
    } else {
        y = 1;
    }
    return y;
}
```

```click
verifying "advance_hidden_branch_fact.c";

int32 advance_hidden_branch_fact(int32 x) {
    ensures result <= 1 by {
        execute_step();
        advance(statement(1).exit)
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
fail: simplified proposition was not true
```
