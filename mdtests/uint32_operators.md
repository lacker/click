# uint32 operators

This covers the scalar `uint32` operators beyond addition and subtraction.
The high-bit division and right-shift cases are intentional: they distinguish
unsigned arithmetic from the signed interpretation of the same 32-bit pattern.

```c filename=uint32_operators.c
uint32 uint32_multiply(uint32 value) {
    return value * 2u;
}

uint32 uint32_divide_high_bit() {
    return 0xffffffffu / 2u;
}

uint32 uint32_remainder_high_bit() {
    return 0xffffffffu % 2u;
}

uint32 uint32_bitwise(uint32 value) {
    return (value & 0xffu) | (value ^ 0xffffffffu);
}

uint32 uint32_bitwise_not() {
    return ~0u;
}

uint32 uint32_shift_left() {
    return 0x80000000u << 1u;
}

uint32 uint32_logical_shift_right() {
    return 0x80000000u >> 31u;
}

int32 int32_shift_with_uint32_count() {
    return -8 >> 1u;
}

uint32 uint32_compound_assignments() {
    uint32 value = 0xffffffffu;
    value *= 2u;
    value /= 2u;
    value %= 3u;
    value |= 0x80000000u;
    value &= 0xffffffffu;
    value ^= 0x80000000u;
    value <<= 1u;
    value >>= 1u;
    value++;
    value--;
    return value;
}

uint32 uint32_negate() {
    return -1u;
}
```

```click
verifying "uint32_operators.c";

uint32 uint32_multiply(uint32 value) {
    ensures product: result == value * 2u32 by auto;
}

uint32 uint32_divide_high_bit() {
    ensures quotient: result == 2147483647u32 by auto;
}

uint32 uint32_remainder_high_bit() {
    ensures remainder: result == 1u32 by auto;
}

uint32 uint32_bitwise(uint32 value) {
    ensures bitwise: result == (value & 255u32) | (value ^ 4294967295u32) by auto;
}

uint32 uint32_bitwise_not() {
    ensures complement: result == 4294967295u32 by auto;
}

uint32 uint32_shift_left() {
    ensures wrapped: result == 0u32 by auto;
}

uint32 uint32_logical_shift_right() {
    ensures shifted: result == 1u32 by auto;
}

int32 int32_shift_with_uint32_count() {
    ensures shifted: result == -4 by auto;
}

uint32 uint32_compound_assignments() {
    ensures updates: result == 1u32 by auto;
}

uint32 uint32_negate() {
    ensures wrapped: result == 4294967295u32 by auto;
}
```

```expect
pass
```
