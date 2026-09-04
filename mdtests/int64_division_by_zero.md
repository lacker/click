# Signed 64-bit division by zero

The signed 64-bit divisor retains C's division-by-zero undefined behavior.

```c filename=int64_division_by_zero.c
int64_t int64_division_by_zero() {
    return (int64_t)1 / 0;
}
```

```click
verifying "int64_division_by_zero.c";

int64_t int64_division_by_zero() {
    ensures no_result: result == 0 by auto;
}
```

```expect
fail: undefined behavior: division by zero
```
