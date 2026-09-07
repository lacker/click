# binary32 comparison orders negative values below positive ones

Constant float comparison decides an ordering over the stored IEEE payloads.
Those payloads sit in a container wider than every format except binary64, so
the monotone ordering key has to complement a negative encoding inside the
format's own width. Complementing the whole container would raise every
negative binary32 value above every non-negative one.

```c filename=float32_ordering_is_signed.c
int32 mixed_sign_less() {
    float a = -1.0f;
    float b = 1.0f;
    if (a < b) {
        return 1;
    }
    return 0;
}

int32 mixed_sign_greater() {
    float a = -1.0f;
    float b = 1.0f;
    if (a > b) {
        return 1;
    }
    return 0;
}

int32 same_sign_less() {
    float a = -2.5f;
    float b = -1.5f;
    if (a < b) {
        return 1;
    }
    return 0;
}

int32 signed_zero_equal() {
    float a = -0.0f;
    float b = 0.0f;
    if (a == b) {
        return 1;
    }
    return 0;
}

int32 double_mixed_sign_less() {
    double a = -1.0;
    double b = 1.0;
    if (a < b) {
        return 1;
    }
    return 0;
}
```

```click
verifying "float32_ordering_is_signed.c";

int32 mixed_sign_less() {
    ensures result == 1 by auto;
}

int32 mixed_sign_greater() {
    ensures result == 0 by auto;
}

int32 same_sign_less() {
    ensures result == 1 by auto;
}

int32 signed_zero_equal() {
    ensures result == 1 by auto;
}

int32 double_mixed_sign_less() {
    ensures result == 1 by auto;
}
```

```expect
pass
```
