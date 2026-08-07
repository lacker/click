# branch requires a C if at the frontier

```c filename=branch_requires_if.c
int32 branch_requires_if(int32 x) {
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
verifying "branch_requires_if.c";

int32 branch_requires_if(int32 x) {
    ensures result >= 0 by {
        branch {
            then {
            }
            else {
            }
        }
    }
}
```

```expect
fail: `branch` requires a C `if` at the execution frontier
```
