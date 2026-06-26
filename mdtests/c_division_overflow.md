# C division overflow

This checks the one signed `int32` division overflow case: `INT_MIN / -1`.

```c filename=divide_overflow.c
int32 divide_overflow() {
    return ~2147483647 / ~0;
}
```

```click
verifying "divide_overflow.c";

int32 divide_overflow() {
    ensures no_wrapping_result: result == 0 by auto;
}
```

```expect
fail: outcome was UndefinedBehavior(SignedOverflow)
```
