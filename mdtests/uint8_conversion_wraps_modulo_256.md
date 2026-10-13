# Conversion to `unsigned char` wraps modulo 256

C11 6.3.1.3p2 converts an integer to an unsigned type by reducing it modulo
one more than the type's maximum, and GCC and Clang do so. Click gives every
conversion to `unsigned char` that value and owes no range: -56 becomes 200,
300 becomes 44, and a `signed char` -1 becomes 255.

```c filename=uint8_conversion_wraps_modulo_256.c
unsigned char cast(int x) { return (unsigned char)x; }
unsigned char returned(int x) { return x; }
int initialized(int x) { unsigned char c = x; return c; }
unsigned char from_signed_char(signed char c) { return c; }
```

```click
verifying "uint8_conversion_wraps_modulo_256.c";

unsigned char cast(int32 x) {
    requires x == -56;
    ensures result == 200;
} by { execute(); simp(); }

unsigned char returned(int32 x) {
    requires x == 300;
    ensures result == 44;
} by { execute(); simp(); }

int32 initialized(int32 x) {
    requires x == -1;
    ensures result == 255;
} by { execute(); simp(); }

unsigned char from_signed_char(signed char c) {
    requires c == -1;
    ensures result == 255;
} by { execute(); simp(); }
```

```expect
pass
```
