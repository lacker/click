# Branch interfaces compose with forward execution

The common interface exported by a branch is the input to the ordinary
forward proof that follows it.

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
        step();
        branch {
            ensuring {
                fact y >= 0;
                fact y < 2147483647;
            }
            then {
                step();
            }
            else {
                step();
            }
        }
        step() using {
            y < 2147483647;
        }
        step();
        simp();
    }
}
```

```expect
pass
```
