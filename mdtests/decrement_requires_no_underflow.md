# decrement with a numeric precondition

This checks the corresponding signed-subtraction case: `x > 0` rules out
underflow for `x - 1`.

```c filename=decrement.c
int32 decrement(int32 x) {
    return x - 1;
}
```

```click
verifying "decrement.c";

int32 decrement(int32 x) {
    requires x > 0;
    ensures decrements: result == x - 1 by auto;
}
```

```expect
pass
```

