# advance exports a memory and resource interface

The common store is checked from the exported bounds and owned memory resource,
not from either branch's concrete memory state.

```c filename=advance_memory_interface.c
int32 advance_memory_interface(int32* p, int32 x) {
    if (x >= 0) {
        p[0] = x;
    } else {
        p[0] = 0;
    }
    p[0] = p[0] + 1;
    return p[0];
}
```

```click
verifying "advance_memory_interface.c";

int32 advance_memory_interface(int32* p, int32 x) {
    requires x < 2147483647;
    owns p[0..1];

    ensures result > 0 by {
        advance(statement(0).exit)
        ensuring {
            fact p[0] >= 0;
            fact p[0] < 2147483647;
            owns p[0..1];
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
        execute_step();
        simp();
    }
}
```

```expect
pass
```
