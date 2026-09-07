# cancelling float arithmetic keeps an exact result exact

An IEEE result is encoded with its leading significand bit implicit, so the
significand has to be normalized to the format's precision before the fraction
field is taken. Cancelling subtraction and division can produce far fewer
significant bits than that; without the normalization those results encode one
unit too large.

All of these are exact in binary32 or binary64, and each expectation matches
what a C compiler on the same profile computes.

```c filename=float_cancellation_is_exact.c
int32 cancel_double() {
    double x = 1.0 - 0.96875;
    if (x == 0.03125) {
        return 1;
    }
    return 0;
}

int32 cancel_float() {
    float x = 1.0f - 0.96875f;
    if (x == 0.03125f) {
        return 1;
    }
    return 0;
}

int32 divide_exact() {
    double x = 1.0 / 4.0;
    if (x == 0.25) {
        return 1;
    }
    return 0;
}

int32 subtract_to_zero() {
    double x = 1.0 - 1.0;
    if (x == 0.0) {
        return 1;
    }
    return 0;
}

int32 add_without_cancellation() {
    double x = 1.5 + 2.25;
    if (x == 3.75) {
        return 1;
    }
    return 0;
}

int32 multiply_without_cancellation() {
    double x = 1.5 * 2.5;
    if (x == 3.75) {
        return 1;
    }
    return 0;
}
```

```click
verifying "float_cancellation_is_exact.c";

int32 cancel_double() {
    ensures result == 1 by auto;
}

int32 cancel_float() {
    ensures result == 1 by auto;
}

int32 divide_exact() {
    ensures result == 1 by auto;
}

int32 subtract_to_zero() {
    ensures result == 1 by auto;
}

int32 add_without_cancellation() {
    ensures result == 1 by auto;
}

int32 multiply_without_cancellation() {
    ensures result == 1 by auto;
}
```

```expect
pass
```
