# Conversion of a `long` to `int` wraps modulo 2^32

GCC and Clang convert a `long` outside the `int` range by keeping its low 32
bits, read as signed: the value modulo 2^32 in `-2^31..2^31-1`. Click gives
the conversion that value and owes no range: 2^31 becomes -2^31 and
2^32 + 5 becomes 5.

```c filename=int32_conversion_from_a_long_wraps_modulo_2_to_the_32.c
int cast(long x) { return (int)x; }
int returned(long x) { return x; }
```

```click
verifying "int32_conversion_from_a_long_wraps_modulo_2_to_the_32.c";

int32 cast(int64 x) {
    requires x == 2147483648;
    ensures result == -2147483648;
} by { execute(); simp(); }

int32 returned(int64 x) {
    requires x == 4294967301;
    ensures result == 5;
} by { execute(); simp(); }
```

```expect
pass
```
