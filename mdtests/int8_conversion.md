# Signed byte values, promotion, and checked conversion

Signed bytes occupy one byte and promote to `int32` before arithmetic.
Conversions into a signed byte require the range -128 through 127.

```c filename=int8_conversion.c
#include <stdint.h>

int promote(signed char value) { return value + 1; }
int negative_ops(int8_t value) { return value * 2 - 1; }
int complement(signed char value) { return ~value; }
int compare(signed char value) { return value < 0; }
signed char narrow(int value) { return (signed char)value; }
int8_t identity(int8_t value) { return value; }
short widen(signed char value) { return value; }
signed char from_short(short value) { return value; }
signed char from_unsigned(unsigned char value) { return value; }
unsigned char to_unsigned(signed char value) { return value; }
long widen_long(signed char value) { return value; }
signed char minimum(void) { return -128; }
signed char maximum(void) { return 127; }
int widths(void) { return sizeof(signed char) + sizeof(int8_t); }
int local_array(void) {
    signed char values[2];
    values[0] = -128;
    values[1] = 127;
    return values[0] + values[1];
}
struct bytes { signed char first; signed char second; int tail; };
int fields(struct bytes *p) { return p->first + p->second; }
int read_byte(signed char *p) { return p[1]; }
```

```click
verifying "int8_conversion.c";

int promote(signed char value) { ensures result == value + 1 by auto; }
int negative_ops(int8_t value) {
    ensures result == value * 2 - 1 by {
        execute();
        simp();
    }
}
int complement(signed char value) { ensures result == ~value by auto; }
int compare(signed char value) { requires value == -1; ensures result == 1 by auto; }
signed char narrow(int value) {
    requires value >= -128;
    requires value <= 127;
    ensures result == value by auto;
}
int8_t identity(int8_t value) { ensures result == value by auto; }
short widen(signed char value) { ensures result == value by auto; }
signed char from_short(short value) {
    requires value >= -128;
    requires value <= 127;
    ensures result == value by auto;
}
signed char from_unsigned(unsigned char value) {
    requires value <= 127;
    ensures result == value by auto;
}
unsigned char to_unsigned(signed char value) {
    requires value >= 0;
    ensures result == value by auto;
}
long widen_long(signed char value) { ensures result == value by auto; }
signed char minimum() { ensures result == -128 by auto; }
signed char maximum() { ensures result == 127 by auto; }
int widths() { ensures result == 2 by auto; }
int local_array() { ensures result == -1 by auto; }
int fields(struct bytes *p) {
    consumes p->first;
    consumes p->second;
    ensures result == p->first + p->second by auto;
    produces p->first;
    produces p->second;
}
int read_byte(signed char *p) {
    views p[0..2];
    ensures result == p[1] by auto;
}
```

```expect
pass
```
