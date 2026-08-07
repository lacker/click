# branch proofs continue at their shared frontier

After both arms reach the end of an `if`, the surrounding proof continues at
their shared frontier and writes the common suffix once.

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
        step();
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
