# in-range float to integer conversions truncate toward zero

The companion to `float_to_integer_out_of_range_rejected.md`: values whose
truncation fits the destination still fold, including both endpoints of the
`int32` range.

```c filename=float_to_integer_in_range.c
int32 at_maximum() {
    double d = 2147483647.0;
    return (int32) d;
}

int32 at_minimum() {
    double d = -2147483648.0;
    return (int32) d;
}

int32 truncates_toward_zero() {
    double d = 1.9;
    return (int32) d;
}

int32 truncates_negative_toward_zero() {
    double d = -1.9;
    return (int32) d;
}
```

```click
verifying "float_to_integer_in_range.c";

int32 at_maximum() {
    ensures result == 2147483647 by auto;
}

int32 at_minimum() {
    ensures result == -2147483648 by auto;
}

int32 truncates_toward_zero() {
    ensures result == 1 by auto;
}

int32 truncates_negative_toward_zero() {
    ensures result == -1 by auto;
}
```

```expect
pass
```
