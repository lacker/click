# widening binary32 to binary64 preserves infinities

A `float` to `double` conversion is exact: every binary32 value, including the
infinities and NaNs, is representable in binary64. The exceptional branch must
not set a fraction bit on an infinity, which would turn it into a NaN.

```c filename=float_widening_preserves_infinity.c
int32 widen_infinity() {
    float f = INFINITYF;
    double d = (double) f;
    if (isinf(d)) {
        return 1;
    }
    return 0;
}

int32 widen_infinity_is_not_nan() {
    float f = INFINITYF;
    double d = (double) f;
    if (isnan(d)) {
        return 1;
    }
    return 0;
}

int32 widen_negative_infinity_keeps_sign() {
    float f = -INFINITYF;
    double d = (double) f;
    if (d < 0.0) {
        return 1;
    }
    return 0;
}

int32 widen_nan() {
    float f = NANF;
    double d = (double) f;
    if (isnan(d)) {
        return 1;
    }
    return 0;
}

int32 widen_finite() {
    float f = 1.5f;
    double d = (double) f;
    if (d == 1.5) {
        return 1;
    }
    return 0;
}
```

```click
verifying "float_widening_preserves_infinity.c";

int32 widen_infinity() {
    ensures result == 1 by auto;
}

int32 widen_infinity_is_not_nan() {
    ensures result == 0 by auto;
}

int32 widen_negative_infinity_keeps_sign() {
    ensures result == 1 by auto;
}

int32 widen_nan() {
    ensures result == 1 by auto;
}

int32 widen_finite() {
    ensures result == 1 by auto;
}
```

```expect
pass
```
