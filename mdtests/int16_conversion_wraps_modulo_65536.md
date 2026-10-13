# Conversion to `short` wraps modulo 65536

GCC and Clang convert an `int` outside `-32768..32767` to `short` by
reducing it modulo 65536 into that range. Click gives the conversion that
value and owes no range: 40000 becomes -25536 and -32769 becomes 32767.

```c filename=int16_conversion_wraps_modulo_65536.c
short cast(int x) { return (short)x; }
int initialized(int x) { short s = x; return s; }
short from_unsigned_short(unsigned short u) { return u; }
```

```click
verifying "int16_conversion_wraps_modulo_65536.c";

short cast(int32 x) {
    requires x == 40000;
    ensures result == -25536;
} by { execute(); simp(); }

int32 initialized(int32 x) {
    requires x == -32769;
    ensures result == 32767;
} by { execute(); simp(); }

short from_unsigned_short(unsigned short u) {
    requires u == 65535;
    ensures result == -1;
} by { execute(); simp(); }
```

```expect
pass
```
