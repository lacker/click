# Invalid 64-bit shift

The shift count is checked against the 64-bit operand width.

```c filename=int64_invalid_shift.c
int64_t int64_invalid_shift() {
    return (int64_t)1 << 64;
}
```

```click
verifying "int64_invalid_shift.c";

int64_t int64_invalid_shift() {
    ensures no_result: result == 0 by auto;
}
```

```expect
fail: undefined behavior: invalid shift
```
