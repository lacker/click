# Proof marks survive branch joins

A mark made before a C branch remains available after a checked branch join,
including when an `ensuring` interface abstracts arm-local state.

```c filename=proof_mark_survives_branch_join.c
int32 choose(int32 x, int32 flag) {
    if (flag) {
        x = 1;
    } else {
        x = 2;
    }
    return x;
}
```

```click
verifying "proof_mark_survives_branch_join.c";

int32 choose(int32 x, int32 flag) {
    ensures at(function_start, x) == old(x) by {
        mark function_start;
        branch {
            ensuring {
                fact at(function_start, x) == old(x);
            }
            then {
                step();
            }
            else {
                step();
            }
        }
        execute();
        simp();
    }
}
```

```expect
pass
```
