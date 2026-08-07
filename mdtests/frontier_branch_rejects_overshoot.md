# branch arms stop at their shared continuation

```c filename=branch_overshoot.c
int32 branch_overshoot(int32 x) {
    int32 y;
    if (x > 0) {
        y = 1;
    } else {
        y = 0;
    }
    return y;
}
```

```click
verifying "branch_overshoot.c";

int32 branch_overshoot(int32 x) {
    ensures result >= 0 by {
        step();
        branch {
            then {
                step();
                step();
            }
            else {
                step();
                step();
            }
        }
    }
}
```

```expect
fail: arm of `branch` must stop at the shared continuation
```
