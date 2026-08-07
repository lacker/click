# branch preserves a common memory interface

The common store is checked from the facts and owned memory resource preserved
across both branch arms.

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
        branch {
            then {
                step();
            }
            else {
                step();
            }
        }
        step();
        step();
        simp();
    }
}
```

```expect
pass
```
