# sequential branch continuations compose

```c filename=advance_sequential_joins.c
int32 advance_sequential_joins(int32 x) {
    int32 y;
    int32 z;
    if (x >= 0) {
        y = x;
    } else {
        y = 0;
    }
    if (y > 0) {
        z = y;
    } else {
        z = 0;
    }
    return z;
}
```

```click
verifying "advance_sequential_joins.c";

int32 advance_sequential_joins(int32 x) {
    ensures result >= 0 by {
        step();
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
        branch {
            ensuring {
                fact z >= 0;
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
