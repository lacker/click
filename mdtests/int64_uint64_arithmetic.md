# 64-bit integer arithmetic and conversion

This covers the remaining scalar integer widths. Signed `int64_t` arithmetic
keeps its overflow and invalid-shift obligations, while `uint64_t` arithmetic
uses 64-bit modular and unsigned semantics. The casts exercise the widening
and signed-to-unsigned conversions used at C assignment and return boundaries.

```c filename=int64_uint64_arithmetic.c
#include <stdint.h>

int64_t int64_add() {
    return 1LL + 2LL;
}

int64_t int64_multiply() {
    return 3LL * 3LL;
}

int64_t int64_subtract() {
    return 7LL - 2LL;
}

int64_t int64_divide() {
    return 5LL / 2LL;
}

int64_t int64_remainder() {
    return 5LL % 2LL;
}

int32_t int64_compare() {
    return (int64_t)-1 < (int64_t)0;
}

int64_t int64_shift_right() {
    return (int64_t)-4 >> 1;
}

int64_t int64_shift_left() {
    return 1LL << 62;
}

int64_t int64_bitwise() {
    return (0xffLL & 0x0fLL) | (0x10LL ^ 0x03LL);
}

int64_t int64_bitwise_not() {
    return ~0LL;
}

uint64_t uint64_wrap() {
    return 18446744073709551615ULL + 1ULL;
}

uint64_t uint64_subtract() {
    return 0ULL - 1ULL;
}

uint64_t uint64_multiply() {
    return 3ULL * 3ULL;
}

uint64_t uint64_divide_high_bit() {
    return 18446744073709551615ULL / 2ULL;
}

uint64_t uint64_remainder_high_bit() {
    return 18446744073709551615ULL % 2ULL;
}

uint64_t uint64_bitwise() {
    return (0xffULL & 0x0fULL) | (0x8000000000000000ULL >> 63);
}

uint64_t uint64_shift_left() {
    return 1ULL << 63;
}

int32_t uint64_compare() {
    return 18446744073709551615ULL > 1ULL;
}

uint64_t uint64_from_int64(int64_t value) {
    return (uint64_t)value;
}

int64_t int64_from_int32(int32_t value) {
    return (int64_t)value;
}

int64_t int64_from_uint32(uint32_t value) {
    return (int64_t)value;
}

uint64_t uint64_from_int32(int32_t value) {
    return (uint64_t)value;
}

uint64_t uint64_from_uint32(uint32_t value) {
    return (uint64_t)value;
}

long long long_long_identity(long long value) {
    return value;
}

size_t size_identity(size_t value) {
    return value;
}

size_t size_add() {
    return (size_t)1 + (size_t)2;
}

ssize_t ssize_identity(ssize_t value) {
    return value;
}
```

```click
verifying "int64_uint64_arithmetic.c";

int64_t int64_add() {
    ensures sum: result == 3 by auto;
}

int64_t int64_multiply() {
    ensures product: result == 9 by auto;
}

int64_t int64_subtract() {
    ensures difference: result == 5 by auto;
}

int64_t int64_divide() {
    ensures quotient: result == 2 by auto;
}

int64_t int64_remainder() {
    ensures remainder: result == 1 by auto;
}

int32_t int64_compare() {
    ensures comparison: result == 1 by auto;
}

int64_t int64_shift_right() {
    ensures shifted: result == -2 by auto;
}

int64_t int64_shift_left() {
    ensures shifted: result == 4611686018427387904i64 by auto;
}

int64_t int64_bitwise() {
    ensures bitwise: result == 31i64 by auto;
}

int64_t int64_bitwise_not() {
    ensures complement: result == -1 by auto;
}

uint64_t uint64_wrap() {
    ensures wrapped: result == 0u64 by auto;
}

uint64_t uint64_subtract() {
    ensures difference: result == 18446744073709551615u64 by auto;
}

uint64_t uint64_multiply() {
    ensures product: result == 9u64 by auto;
}

uint64_t uint64_divide_high_bit() {
    ensures quotient: result == 9223372036854775807u64 by auto;
}

uint64_t uint64_remainder_high_bit() {
    ensures remainder: result == 1u64 by auto;
}

uint64_t uint64_bitwise() {
    ensures bitwise: result == 15u64 by auto;
}

uint64_t uint64_shift_left() {
    ensures shifted: result == 9223372036854775808u64 by auto;
}

int32_t uint64_compare() {
    ensures comparison: result == 1 by auto;
}

uint64_t uint64_from_int64(int64_t value) {
    ensures converted: result == value by auto;
}

int64_t int64_from_int32(int32_t value) {
    ensures widened: result == value by auto;
}

int64_t int64_from_uint32(uint32_t value) {
    ensures widened: result == value by auto;
}

uint64_t uint64_from_int32(int32_t value) {
    ensures widened: result == value by auto;
}

uint64_t uint64_from_uint32(uint32_t value) {
    ensures widened: result == value by auto;
}

int64_t long_long_identity(int64_t value) {
    ensures identity: result == value by auto;
}

size_t size_identity(size_t value) {
    ensures identity: result == value by auto;
}

size_t size_add() {
    ensures sum: result == 3u64 by auto;
}

ssize_t ssize_identity(ssize_t value) {
    ensures identity: result == value by auto;
}
```

```expect
pass
```
