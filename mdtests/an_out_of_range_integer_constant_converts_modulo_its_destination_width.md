# An out-of-range integer constant converts modulo its destination width

GCC and Clang accept an integer constant converted to an integer type that
cannot represent it, at most with a `-Woverflow` or `-Wconstant-conversion`
warning, and give it the value reduced modulo 2^N into the type's range: C11
6.3.1.3p2 defines this for an unsigned type, and GCC defines the
implementation-defined signed conversion the same way. Click converts such a
constant the same way in an automatic or static initializer, an array
initializer, an assignment, a store, an explicit cast, a `return`, and a call
argument. Under the default x86_64-linux-userspace target plain `char` is
signed, so `char c = 200` holds `-56`.

```c filename=an_out_of_range_integer_constant_converts_modulo_its_destination_width.c
static const signed char table[2] = {200, -129};

int initialize(void) {
    unsigned char c = -56;
    return c;
}

int assign(void) {
    unsigned char c;
    c = 300;
    return c;
}

int narrow_signed(void) {
    signed char c = 200;
    short s = 40000;
    char plain = 200;
    return c + s + plain;
}

int read_table(void) { return table[0] + table[1]; }

int array(void) {
    unsigned char bytes[2] = {-1, 256};
    return bytes[0] + bytes[1];
}

void store(unsigned char *p) { *p = -56; }

unsigned char cast(void) { return (unsigned char)-2; }

unsigned short returned(void) { return -1; }

unsigned int widen(unsigned char c) { return c; }

unsigned int argument(void) { return widen(-56); }

unsigned int wide(void) {
    unsigned int u = -1;
    int i = 4294967295U;
    return u + i;
}
```

```click
verifying "an_out_of_range_integer_constant_converts_modulo_its_destination_width.c";

int initialize() { ensures result == 200 by auto; }
int assign() { ensures result == 44 by auto; }
int narrow_signed() { ensures result == -56 + -25536 + -56 by auto; }
int read_table() { ensures result == -56 + 127 by auto; }
int array() { ensures result == 255 by auto; }
void store(uint8 *p) {
    requires viewable(p[0..1]);
    consumes p[0..1];
    produces p[0..1];
    ensures p[0] == 200 by auto;
}
uint8 cast() { ensures result == 254 by auto; }
uint16 returned() { ensures result == 65535 by auto; }
uint32 widen(uint8 c) { ensures result == c by auto; }
uint32 argument() { ensures result == 200 by auto; }
uint32 wide() { ensures result == 4294967294 by auto; }
```

```expect
pass
```
