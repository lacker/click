# Conversion of an `unsigned long` to `int` wraps modulo 2^32

GCC and Clang convert an `unsigned long` above `INT_MAX` to `int` by keeping
its low 32 bits, read as signed. Click gives the conversion that value and
owes no range: `ULONG_MAX` becomes -1 and 2^31 becomes -2^31.

```c filename=int32_conversion_from_an_unsigned_long_wraps_modulo_2_to_the_32.c
int cast(unsigned long x) { return (int)x; }
int returned(unsigned long x) { return x; }
```

```click
verifying "int32_conversion_from_an_unsigned_long_wraps_modulo_2_to_the_32.c";

int32 cast(uint64 x) {
    requires x == 18446744073709551615u64;
    ensures result == -1;
} by { execute(); simp(); }

int32 returned(uint64 x) {
    requires x == 2147483648u64;
    ensures result == -2147483648;
} by { execute(); simp(); }
```

```expect
pass
```
