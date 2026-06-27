# C shift large count

This checks that a shift count greater than or equal to the `int32` width is
undefined behavior.

```c filename=shift_large_count.c
int32 shift_large_count() {
    return 1 << 32;
}
```

```click
verifying "shift_large_count.c";

int32 shift_large_count() {
    ensures no_result: result == 0 by auto;
}
```

```expect
fail: outcome was UndefinedBehavior(InvalidShift)
```
