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
            ensuring {
                fact y >= 0;
            }
            then {
                step();
                branch {
                    ensuring {
                        fact y >= 0;
                    }
                    then {
                        step();
                        have y >= 0 by {
                            apply(int32_increment_greater_equal_lower_bound(at(statement(1).entry, x), at(statement(1).entry, 0), at(function.entry, 2147483647))) using {
                                at(statement(1).entry, x) >= at(statement(1).entry, 0);
                                at(function.entry, x < 2147483647);
                            }
                        }
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
        have result >= 0 by {
            assumption();
        }
        assumption();
    }
}
```

```expect
pass
```
