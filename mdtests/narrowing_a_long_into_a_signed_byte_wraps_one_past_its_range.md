# Narrowing a long into a signed byte wraps one past its range

`(signed char)value` from a `long` is the value modulo 256 in `-128..127`, as
GCC and Clang compute it, and owes no range. One past the upper end, 128,
becomes -128; the last value inside the range is itself.

```c filename=long_to_signed_byte.c
signed char narrow(long value) { return (signed char)value; }
```

```click
verifying "long_to_signed_byte.c";

signed char narrow(long value) {
    requires value >= -128;
    requires value <= 128;
    ensures result >= -128;
    ensures value == 128 implies result == -128;
    ensures value == 127 implies result == 127;
} by { execute(); simp(); }
```

```expect
pass
```
