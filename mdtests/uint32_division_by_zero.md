# uint32 division by zero

Unsigned division and remainder retain C's division-by-zero undefined
behavior; unsigned arithmetic does not turn a zero divisor into a value.

```c filename=uint32_division_by_zero.c
uint32 uint32_division_by_zero() {
    return 1u / 0u;
}
```

```click
verifying "uint32_division_by_zero.c";

uint32 uint32_division_by_zero() {
    ensures no_result: result == 0u32 by auto;
}
```

```expect
fail: undefined behavior: division by zero
```
