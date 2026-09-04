# uint32 invalid shift

The shift count is checked against the 32-bit width using its own unsigned
type. A `uint32` count of 32 is invalid even though its signed bit pattern is
nonnegative.

```c filename=uint32_invalid_shift.c
uint32 uint32_invalid_shift() {
    return 1u << 32u;
}
```

```click
verifying "uint32_invalid_shift.c";

uint32 uint32_invalid_shift() {
    ensures no_result: result == 0u32 by auto;
}
```

```expect
fail: undefined behavior: invalid shift
```
