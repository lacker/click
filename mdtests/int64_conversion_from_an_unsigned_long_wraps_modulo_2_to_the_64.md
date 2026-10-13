# Conversion of an `unsigned long` to `long` wraps modulo 2^64

GCC and Clang convert an `unsigned long` above `LONG_MAX` to `long` by
reading the same 64 bits as signed: the value modulo 2^64. Click gives the
conversion that value and owes no range: `ULONG_MAX` becomes -1 and 2^63
becomes `LONG_MIN`.

```c filename=int64_conversion_from_an_unsigned_long_wraps_modulo_2_to_the_64.c
long cast(unsigned long x) { return (long)x; }
long returned(unsigned long x) { return x; }
```

```click
verifying "int64_conversion_from_an_unsigned_long_wraps_modulo_2_to_the_64.c";

int64 cast(uint64 x) {
    requires x == 18446744073709551615u64;
    ensures result == -1;
} by { execute(); simp(); }

int64 returned(uint64 x) {
    requires x == 9223372036854775808u64;
    ensures result == -9223372036854775808;
} by { execute(); simp(); }
```

```expect
pass
```
