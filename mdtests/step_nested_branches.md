# nested branch steps

Branch execution enters one selected arm without executing its body. This lets
a proof execute statements inside that arm and then select a nested C branch.

```c filename=nested_branch_steps.c
int32 nested_branch_steps(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
        if (y > 0) {
            y = y + 1;
        } else {
            y = 0;
        }
    } else {
        y = 0;
    }
    return y;
}
```

```click
verifying "nested_branch_steps.c";

int32 nested_branch_steps(int32 x) {
    requires x < 2147483647;

    ensures result >= 0 by {
        step();
        if x >= 0 {
            step();
            step();
            if y > 0 {
                step();
                step();
                step();
                simp();
            } else {
                step();
                step();
                step();
                simp();
            }
        } else {
            step();
            step();
            step();
            simp();
        }
    }
}
```

```expect
pass
```
