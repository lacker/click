# C shift negative count

This checks that a negative shift count is undefined behavior.

```c filename=shift_negative_count.c
int32 shift_negative_count() {
    return 1 << ~0;
}
```

```click
verifying "shift_negative_count.c";

int32 shift_negative_count() {
    ensures no_result: result == 0 by auto;
}
```

```expect
fail: outcome was UndefinedBehavior(InvalidShift)
```
