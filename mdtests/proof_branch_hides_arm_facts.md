# Branch ensuring hides arm-specific facts

Although the two concrete branches assign `0` and `1`, the exported lower
bound alone does not preserve either arm-specific upper-bound fact.

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
        step();
        simp();
    }
}
```

```expect
fail: unclosed goal: result <= 1
```
