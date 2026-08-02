# proof if inside have

A scoped `have` proof can establish a pure fact by cases and then return that
fact to the surrounding proof, which continues execution normally.

```c filename=sign_partition.c
int32 sign_partition(int32 x) {
    int32 y;
    y = x;
    return y;
}
```

```click
verifying "sign_partition.c";

int32 sign_partition(int32 x) {
    ensures result <= 0 or result > 0 by {
        step();
        step();
        have y <= 0 or y > 0 by {
            if y <= 0 {
                simp();
            } else {
                simp();
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
