# advance joins branch proofs at a program point

`advance` proves that every internal proof case reaches the declared target
with the same asserted facts. The surrounding proof then writes the common
suffix once.

```c filename=joined_increment.c
int32 joined_increment(int32* p, int32 x) {
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
verifying "joined_increment.c";

int32 joined_increment(int32* p, int32 x) {
    requires x < 2147483647;
    owns p[0..1];

    ensures result > 0 by {
        execute_step();
        advance(statement(1).exit)
        ensuring {
            fact y >= 0;
            fact y < 2147483647;
            owns p[0..1];
            views p[0..1];
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
