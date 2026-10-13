# A cast identity bound outside the signed-byte range is refused

`integer_cast_identity` relates a narrowed `long` to its source only when the
named bounds lie inside the destination range. A bound of `128` is one past
`signed char`'s range.

```c filename=cast_identity_range.c
signed char narrow(long value) { return (signed char)value; }
```

```click
verifying "cast_identity_range.c";

signed char narrow(long value) {
    requires value >= -128;
    requires value <= 127;
    requires -128 <= to_integer(value);
    requires to_integer(value) <= 128;
    ensures to_integer(result) == to_integer(value);
} by {
    execute();
    arithmetic_certificate rules {
        premise 0: -128 <= to_integer(old(value)) => -128 <= to_integer(old(value));
        premise 1: to_integer(old(value)) <= 128 => to_integer(old(value)) <= 128;
        integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(old(value));
        conclusion 0;
    }
}
```

```expect
fail: arithmetic_certificate
```
