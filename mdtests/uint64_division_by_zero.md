# Unsigned 64-bit division by zero

Unsigned 64-bit division and remainder retain C's division-by-zero undefined
behavior.

```c filename=uint64_division_by_zero.c
uint64_t uint64_division_by_zero() {
    return 1ULL / 0ULL;
}
```

```click
verifying "uint64_division_by_zero.c";

uint64_t uint64_division_by_zero() {
    ensures no_result: result == 0u64 by auto;
}
```

```expect
fail: undefined behavior: division by zero
```
