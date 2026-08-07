# nested branch steps

Frontier-local `branch` mirrors nested C control flow. Once both arms reach the
same continuation, the following proof is written once.

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
        branch {
            then {
                step();
                branch {
                    then {
                        step();
                    }
                    else {
                        step();
                    }
                }
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
