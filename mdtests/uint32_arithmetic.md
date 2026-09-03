# uint32 arithmetic and unsigned comparison

This checks a 32-bit unsigned scalar without changing the existing signed
`int32` overflow rules. Addition is defined to wrap at 2^32, and ordered
comparisons use unsigned order rather than interpreting the bit pattern as a
signed value.

```c filename=uint32_arithmetic.c
uint32 uint32_add(uint32 a, uint32 b) {
    return a + b;
}

uint32 uint32_wrap_from_local(uint32 value) {
    uint32 current;
    current = value;
    current += 4294967295u;
    return current + 1;
}

uint32 uint32_wrap_constant() {
    return 4294967295u + 1;
}

unsigned int uint32_unsigned_int(unsigned int value) {
    return value + 1;
}

uint32_t uint32_stdint(uint32_t value) {
    return value + 1;
}

int32 uint32_is_less(uint32 a, uint32 b) {
    return a < b;
}

int32 uint32_high_bit_is_not_less_than_one() {
    return 0xffffffffu < 1;
}
```

```click
verifying "uint32_arithmetic.c";

uint32 uint32_add(uint32 a, uint32 b) {
    ensures sum: result == a + b by auto;
}

uint32 uint32_wrap_from_local(uint32 value) {
    ensures sum: result == value + 4294967295u32 + 1u32 by auto;
}

uint32 uint32_wrap_constant() {
    ensures wrapped: result == 0u32 by auto;
}

uint32 uint32_unsigned_int(uint32 value) {
    ensures increment: result == value + 1u32 by auto;
}

uint32 uint32_stdint(uint32 value) {
    ensures increment: result == value + 1u32 by auto;
}

int32 uint32_is_less(uint32 a, uint32 b) {
    ensures comparison: result == 0 or result == 1 by auto;
}

int32 uint32_high_bit_is_not_less_than_one() {
    ensures comparison: result == 0 by auto;
}

theorem uint32_unsigned_order() {
    ensures 2147483648u32 > 1u32 by auto;
}
```

```expect
pass
```
