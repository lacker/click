# Conversion to `unsigned short` wraps modulo 65536

C11 6.3.1.3p2 converts an integer to `unsigned short` modulo 65536, and GCC
and Clang do so. Click gives the conversion that value and owes no range:
-1 becomes 65535 and 70000 becomes 4464.

```c filename=uint16_conversion_wraps_modulo_65536.c
unsigned short cast(int x) { return (unsigned short)x; }
int initialized(int x) { unsigned short u = x; return u; }
```

```click
verifying "uint16_conversion_wraps_modulo_65536.c";

unsigned short cast(int32 x) {
    requires x == -1;
    ensures result == 65535;
} by { execute(); simp(); }

int32 initialized(int32 x) {
    requires x == 70000;
    ensures result == 4464;
} by { execute(); simp(); }
```

```expect
pass
```
