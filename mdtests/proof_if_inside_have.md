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
    ensures result == x by {
        execute_step();
        execute_step();
        have y <= 0 or y > 0 by {
            if y <= 0 {
                simp();
            } else {
                simp();
            }
        }
        have y <= 0 or y > 0 by {
            simp();
        }
        execute_step();
        simp();
    }
}
```

```expect
pass
```
