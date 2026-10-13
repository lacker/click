# Narrowing a long into a signed byte requires its range

`(signed char)value` from a `long` owes `-128 <= value <= 127`. One past the
upper end is not enough.

```c filename=long_to_signed_byte.c
signed char narrow(long value) { return (signed char)value; }
```

```click
verifying "long_to_signed_byte.c";

signed char narrow(long value) {
    requires value >= -128;
    requires value <= 128;
    ensures result >= -128 by auto;
}
```

```expect
fail: int8 narrowing upper bound
```
