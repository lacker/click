# branch preserving common requirements

An explicit `ensuring` block augments the deterministic common state. It is
not an exhaustive whitelist, so a stable precondition remains available after
the join without being repeated.

```c filename=branch_common_requirement.c
int32 branch_common_requirement(int32 x, int32 flag) {
    int32 y;
    if (flag != 0) {
        y = 0;
    } else {
        y = 1;
    }
    return x;
}
```

```click
verifying "branch_common_requirement.c";

int32 branch_common_requirement(int32 x, int32 flag) {
    requires x >= 0;

    ensures result >= 0 by {
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
pass
```
