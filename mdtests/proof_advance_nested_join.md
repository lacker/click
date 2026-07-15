# nested advance interfaces compose

An outer scoped execution can use an inner abstract frontier and export a
second, stronger interface.

```c filename=advance_nested_join.c
int32 advance_nested_join(int32 x) {
    int32 y;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    y = y + 1;
    return y;
}
```

```click
verifying "advance_nested_join.c";

int32 advance_nested_join(int32 x) {
    requires x < 2147483647;

    ensures result > 0 by {
        advance(statement(4).exit)
        ensuring {
            fact y > 0;
        }
        by {
            execute_step();
            advance(statement(1).exit)
            ensuring {
                fact y >= 0;
                fact y < 2147483647;
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
        }
        execute_step();
        simp();
    }
}
```

```expect
pass
```
