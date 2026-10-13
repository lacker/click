# Integer pointers of either signedness read the same bits

GCC and Clang convert between pointers to the signed and unsigned integer
types of one width, `int *` and `unsigned int *` for example, with only a
`-Wpointer-sign` warning, and C11 6.5p7 lets either type access the object.
Click accepts the conversion, uncast or cast, at one level of indirection,
for 16-, 32-, and 64-bit integers as for the character types. A load reads
the cell's bits in the load's own signedness, and a store through either
pointer writes the bits a later read of the object sees. A contract stated
over `int32` cells accepts a pointer to `uint32` cells.

```c filename=integer_pointers_of_either_signedness_read_the_same_bits.c
unsigned int read_unsigned_word(void) {
    int x = -1;
    unsigned int *q = &x;
    return *q;
}

int read_signed_word(void) {
    unsigned int u = 4000000000u;
    int *p = (int *)&u;
    return *p;
}

unsigned int store_through_signed(void) {
    unsigned int u = 0;
    int *p = &u;
    *p = -2;
    return u;
}

unsigned short read_unsigned_half(void) {
    short s = -56;
    unsigned short *q = &s;
    return *q;
}

short read_signed_half(void) {
    unsigned short u = 65480;
    short *p = &u;
    return *p;
}

unsigned long read_unsigned_long(void) {
    long x = -1;
    unsigned long *q = &x;
    return *q;
}

long read_signed_long(void) {
    unsigned long u = 9223372036854775808ul;
    long *p = (long *)&u;
    return *p;
}

int first(int *p) { return p[0]; }

int pass_unsigned(void) {
    unsigned int u = 4294967295u;
    return first(&u);
}
```

```click
verifying "integer_pointers_of_either_signedness_read_the_same_bits.c";

uint32 read_unsigned_word() { ensures result == 4294967295 by auto; }
int32 read_signed_word() { ensures result == -294967296 by auto; }
uint32 store_through_signed() { ensures result == 4294967294 by auto; }
uint16 read_unsigned_half() { ensures result == 65480 by auto; }
int16 read_signed_half() { ensures result == -56 by auto; }
uint64 read_unsigned_long() { ensures result == 18446744073709551615 by auto; }
int64 read_signed_long() { ensures result == -9223372036854775808 by auto; }
int32 first(int32 *p) {
    views p[0..1];
    ensures result == p[0];
}
int32 pass_unsigned() { ensures result == -1 by auto; }
```

```expect
pass
```
