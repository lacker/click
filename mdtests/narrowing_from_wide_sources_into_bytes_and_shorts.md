# Narrowing from wide sources into bytes and shorts

C converts `short`, `unsigned short`, `unsigned int`, `long` and
`unsigned long` values into `signed char`, `unsigned char`, `short` and
`unsigned short`. Each such conversion owes the destination's range, stated
in the source's own type; inside it the value is unchanged. A 64-bit source
keeps its low word, so relating the narrowed value back to the source uses
the range-checked `integer_cast_identity` rule.

```c filename=wide_narrowing.c
unsigned char byte_from_short(short value) { return (unsigned char)value; }
unsigned char byte_from_ushort(unsigned short value) { return value; }
signed char sbyte_from_uint(unsigned int value) { return (signed char)value; }
unsigned char byte_from_uint(unsigned int value) { return (unsigned char)value; }
short short_from_uint(unsigned int value) { return (short)value; }
unsigned short ushort_from_uint(unsigned int value) { return value; }
signed char sbyte_from_long(long value) { return (signed char)value; }
unsigned char byte_from_ulong(unsigned long value) { return (unsigned char)value; }
short short_from_long(long value) { return value; }
unsigned short ushort_from_ulong(unsigned long value) { return value; }
```

```click
verifying "wide_narrowing.c";

unsigned char byte_from_short(short value) {
    requires value >= 0;
    requires value <= 255;
    ensures result == value by auto;
}
unsigned char byte_from_ushort(unsigned short value) {
    requires value <= 255;
    ensures result == value by auto;
}
signed char sbyte_from_uint(unsigned int value) {
    requires value <= 127u32;
    ensures result == value by auto;
}
unsigned char byte_from_uint(unsigned int value) {
    requires value <= 255u32;
    ensures result == value by auto;
}
short short_from_uint(unsigned int value) {
    requires value <= 32767u32;
    ensures result == value by auto;
}
unsigned short ushort_from_uint(unsigned int value) {
    requires value <= 65535u32;
    ensures result == value by auto;
}
signed char sbyte_from_long(long value) {
    requires value >= -128;
    requires value <= 127;
    requires -128 <= to_integer(value);
    requires to_integer(value) <= 127;
    ensures to_integer(result) == to_integer(value);
} by {
    execute();
    arithmetic_certificate rules {
        premise 0: -128 <= to_integer(old(value)) => -128 <= to_integer(old(value));
        premise 1: to_integer(old(value)) <= 127 => to_integer(old(value)) <= 127;
        integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(old(value));
        conclusion 0;
    }
}
unsigned char byte_from_ulong(unsigned long value) {
    requires value <= 255u64;
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 255;
    ensures to_integer(result) == to_integer(value);
} by {
    execute();
    arithmetic_certificate rules {
        premise 0: 0 <= to_integer(old(value)) => 0 <= to_integer(old(value));
        premise 1: to_integer(old(value)) <= 255 => to_integer(old(value)) <= 255;
        integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(old(value));
        conclusion 0;
    }
}
short short_from_long(long value) {
    requires value >= -32768;
    requires value <= 32767;
    requires -32768 <= to_integer(value);
    requires to_integer(value) <= 32767;
    ensures to_integer(result) == to_integer(value);
} by {
    execute();
    arithmetic_certificate rules {
        premise 0: -32768 <= to_integer(old(value)) => -32768 <= to_integer(old(value));
        premise 1: to_integer(old(value)) <= 32767 => to_integer(old(value)) <= 32767;
        integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(old(value));
        conclusion 0;
    }
}
unsigned short ushort_from_ulong(unsigned long value) {
    requires value <= 65535u64;
    requires 0 <= to_integer(value);
    requires to_integer(value) <= 65535;
    ensures to_integer(result) == to_integer(value);
} by {
    execute();
    arithmetic_certificate rules {
        premise 0: 0 <= to_integer(old(value)) => 0 <= to_integer(old(value));
        premise 1: to_integer(old(value)) <= 65535 => to_integer(old(value)) <= 65535;
        integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(old(value));
        conclusion 0;
    }
}
```

```expect
pass
```
