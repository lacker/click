# A wide argument to a narrow parameter wraps into its range

The caller's side of
`mdtests/a_narrow_parameter_has_its_type_range_at_entry.md`. `widen` assumes
its `uint8` parameter is in `[0, 255]`; that is sound because every call
converts its argument to `uint8`, and C's conversion, as GCC and Clang
perform it, reduces any `int32` modulo 256 into that range. An unbounded
argument therefore needs no range proof, and the callee's result is still in
`[0, 255]`; passing 300 gives 44.
`mdtests/a_bounded_argument_to_a_narrow_parameter_is_in_its_range.md` is the
bounded case.

```c filename=a_wide_argument_to_a_narrow_parameter_wraps_into_its_range.c
int32 widen(uint8 x) {
    return x;
}

int32 pass_wide(int32 y) {
    return widen(y);
}

int32 pass_known(void) {
    return widen(300);
}
```

```click
verifying "a_wide_argument_to_a_narrow_parameter_wraps_into_its_range.c";

int32 widen(uint8 x) {
    ensures result >= 0;
    ensures result <= 255;
    ensures result == x;
} by { execute(); simp(); }

int32 pass_wide(int32 y) {
    ensures result >= 0;
    ensures result <= 255;
} by { execute(); simp(); }

int32 pass_known() {
    ensures result == 44;
} by { execute(); simp(); }
```

```expect
pass
```
