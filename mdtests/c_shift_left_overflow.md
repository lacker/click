# C shift left overflow

This checks that signed left shift is undefined behavior when the result is not
representable as `int32`.

```c filename=shift_left_overflow.c
int32 shift_left_overflow() {
    return 1073741824 << 1;
}
```

```click
verifying "shift_left_overflow.c";

int32 shift_left_overflow() {
    ensures no_wrapping_result: result == 0 by auto;
}
```

```expect
fail: undefined behavior: signed overflow
```
