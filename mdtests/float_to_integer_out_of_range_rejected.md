# a float too large for any integer container has no folded conversion

Converting a floating value whose truncation is outside the destination range
is undefined, so a constant conversion is only folded when the value fits.
Scaling the significand must not drop the bits carried off the top of the
container, which would turn an enormous value into a small in-range one.

`340282366920938463463374607431768211456.0` is 2^128, so its magnitude does
not fit the conversion's own container, let alone `int32`.

```c filename=float_to_integer_out_of_range_rejected.c
int32 float_to_integer_out_of_range_rejected() {
    double d = 340282366920938463463374607431768211456.0;
    int32 v = (int32) d;
    return v;
}
```

```click
verifying "float_to_integer_out_of_range_rejected.c";

int32 float_to_integer_out_of_range_rejected() {
    ensures result == 0;
}
```

```expect
fail: type mismatch
```
