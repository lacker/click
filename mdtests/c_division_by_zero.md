# C division by zero

This checks that C0 signed `int32` division by zero is undefined behavior, not a
wrapping or symbolic value.

```c filename=divide_by_zero.c
int32 divide_by_zero() {
    return 10 / 0;
}
```

```click
verifying "divide_by_zero.c";

int32 divide_by_zero() {
    ensures no_result: result == 0 by auto;
}
```

```expect
fail: undefined behavior: division by zero
```
