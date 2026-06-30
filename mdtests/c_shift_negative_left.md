# C shift negative left operand

This checks the C0 rule that signed left shift requires a nonnegative left
operand.

```c filename=shift_negative_left.c
int32 shift_negative_left() {
    return ~0 << 1;
}
```

```click
verifying "shift_negative_left.c";

int32 shift_negative_left() {
    ensures no_result: result == 0 by auto;
}
```

```expect
fail: undefined behavior: invalid shift
```
