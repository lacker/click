# 16-bit integer promotion and checked conversion

The modeled `short`/`int16_t` and `uint16_t` scalar types occupy two bytes.
Both integer types undergo C integer promotion to `int32` before arithmetic,
and conversions from `int32` into either width are checked by Click.

```c filename=int16_uint16_conversion.c
#include <stdint.h>

int32 signed_short_promotes(short value) {
    short local = value;
    return local + 1;
}

int32 unsigned_short_promotes(uint16_t value) {
    uint16_t local = value;
    return local + 1;
}

int32 signed_short_operators(short value) {
    return value - 2;
}

int32 signed_short_multiply(short value) {
    return value * 3;
}

int32 signed_short_divide(short value) {
    return value / 2;
}

int32 signed_short_remainder(short value) {
    return value % 2;
}

int32 unsigned_short_bitwise(uint16_t value) {
    return (value & 255u) | (value ^ 1023u);
}

int32 unsigned_short_shift(uint16_t value) {
    return value << 1;
}

int32 unsigned_short_right_shift(uint16_t value) {
    return value >> 1;
}

int32 unsigned_short_not(uint16_t value) {
    return ~value;
}

int32 signed_short_compare(short value) {
    return value < 10;
}

short signed_short_compound(short value) {
    value &= 0;
    return value;
}

int32 width_sizes() {
    return sizeof(short) + sizeof(uint16_t);
}

short signed_short_identity(signed short value) {
    return (short)value;
}

uint16_t unsigned_short_identity(uint16_t value) {
    return (uint16_t)value;
}

int16_t int16_t_identity(int16_t value) {
    return value;
}

short checked_signed_narrow(int32 value) {
    return (short)value;
}

uint16_t checked_unsigned_narrow(int32 value) {
    return (uint16_t)value;
}

struct width_fields {
    uint8_t tag;
    short signed_value;
    uint16_t unsigned_value;
    int32_t tail;
};

int32_t read_width_fields(struct width_fields* packet) {
    return packet->signed_value + packet->unsigned_value;
}
```

```click
verifying "int16_uint16_conversion.c";

int32 signed_short_promotes(short value) {
    ensures promoted: result == value + 1 by auto;
}

int32 unsigned_short_promotes(uint16_t value) {
    ensures promoted: result == value + 1 by auto;
}

int32 signed_short_operators(short value) {
    requires value == 5;
    ensures arithmetic: result == value - 2 by auto;
}

int32 signed_short_multiply(short value) {
    requires value == 5;
    ensures multiplication: result == value * 3 by auto;
}

int32 signed_short_divide(short value) {
    requires value == 5;
    ensures division: result == value / 2 by auto;
}

int32 signed_short_remainder(short value) {
    requires value == 5;
    ensures remainder: result == value % 2 by auto;
}

int32 unsigned_short_bitwise(uint16_t value) {
    ensures bitwise: result == (value & 255) | (value ^ 1023) by auto;
}

int32 unsigned_short_shift(uint16_t value) {
    ensures shifted: result == value << 1 by auto;
}

int32 unsigned_short_right_shift(uint16_t value) {
    ensures shifted: result == value >> 1 by auto;
}

int32 unsigned_short_not(uint16_t value) {
    ensures complement: result == ~value by auto;
}

int32 signed_short_compare(short value) {
    requires value == 5;
    ensures comparison: result == 1 by auto;
}

short signed_short_compound(short value) {
    ensures compound: result == 0 by auto;
}

int32 width_sizes() {
    ensures two_byte_scalars: result == 4 by auto;
}

short signed_short_identity(signed short value) {
    ensures identity: result == value by auto;
}

uint16_t unsigned_short_identity(uint16_t value) {
    ensures identity: result == value by auto;
}

int16_t int16_t_identity(int16_t value) {
    ensures identity: result == value by auto;
}

short checked_signed_narrow(int32 value) {
    requires value >= -32768;
    requires value <= 32767;
    ensures narrowed: result == value by auto;
}

uint16_t checked_unsigned_narrow(int32 value) {
    requires value >= 0;
    requires value <= 65535;
    ensures narrowed: result == value by auto;
}

int32 read_width_fields(struct width_fields* packet) {
    requires loadable(packet->signed_value);
    requires loadable(packet->unsigned_value);
    consumes packet->signed_value;
    consumes packet->unsigned_value;
    ensures fields_promote: result == packet->signed_value + packet->unsigned_value by auto;
    produces packet->signed_value;
    produces packet->unsigned_value;
}
```

```expect
pass
```
