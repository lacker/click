# subnormal float division rounds to nearest

The bug-bash subnormal-division regression: the integer-space IEEE evaluator
jammed the division remainder
into bit 0 of a variable-width quotient, so in the subnormal branch the sticky
bit could land exactly on the rounding bit and round one ulp high. The
quotient below must fold to `0x00000017` (`3.2229864679470793e-44f`), not
`0x00000018`.

```c filename=subnormal_float_division_rounded.c
int32 subnormal_divide() {
    float quotient = 4.203895392974451e-45f / 0.12765958905220032f;
    if (quotient == 3.2229864679470793e-44f) {
        return 1;
    }
    if (quotient == 3.363116314379561e-44f) {
        return 2;
    }
    return 0;
}
```

```click
verifying "subnormal_float_division_rounded.c";

int32 subnormal_divide() {
    ensures result == 1;
}
```

```expect
pass
```
