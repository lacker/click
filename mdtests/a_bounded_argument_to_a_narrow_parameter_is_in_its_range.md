# A bounded argument to a narrow parameter is in its range

The bounded companion of
`mdtests/a_wide_argument_to_a_narrow_parameter_wraps_into_its_range.md`: a
`uint8` argument, or an `int32` one the caller tested into `[0, 255]`,
converts to the `uint8` parameter unchanged, and the callee's result is in
the parameter's range.

```c filename=a_bounded_argument_to_a_narrow_parameter_is_in_its_range.c
int32 widen(uint8 x) {
    return x;
}

int32 pass_narrow(uint8 y) {
    return widen(y);
}

int32 pass_checked(int32 y) {
    if (0 <= y && y <= 255) {
        return widen(y);
    }
    return 0;
}
```

```click
verifying "a_bounded_argument_to_a_narrow_parameter_is_in_its_range.c";

int32 widen(uint8 x) {
    ensures result >= 0;
    ensures result <= 255;
} by { execute(); simp(); }

int32 pass_narrow(uint8 y) {
    ensures result >= 0;
    ensures result <= 255;
} by { execute(); simp(); }

int32 pass_checked(int32 y) {
    ensures result >= 0;
    ensures result <= 255;
} by { execute(); simp(); }
```

```expect
pass
```
