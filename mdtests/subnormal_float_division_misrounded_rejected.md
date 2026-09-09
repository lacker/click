# the mis-rounded subnormal quotient is rejected

Companion to `subnormal_float_division_rounded.md`: bugbash §13 folded the
quotient below to `0x00000018`, so `ensures result == 2` verified before the
fix. With correct round-to-nearest the quotient is `0x00000017`, so claiming
the mis-rounded value must fail.

```c filename=subnormal_float_division_misrounded_rejected.c
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
verifying "subnormal_float_division_misrounded_rejected.c";

int32 subnormal_divide() {
    ensures result == 2;
}
```

```expect
fail: unclosed goal
```
