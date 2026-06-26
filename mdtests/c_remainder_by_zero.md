# C remainder by zero

This checks that C0 signed `int32` remainder by zero follows the same undefined
behavior path as division by zero.

```c filename=remainder_by_zero.c
int32 remainder_by_zero() {
    return 10 % 0;
}
```

```click
verifying "remainder_by_zero.c";

int32 remainder_by_zero() {
    ensures no_result: result == 0 by auto;
}
```

```expect
fail: outcome was UndefinedBehavior(DivisionByZero)
```
