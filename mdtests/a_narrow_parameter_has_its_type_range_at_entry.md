# A narrow parameter has its type range at entry

A `uint8` parameter is in `[0, 255]` from the function's first statement:
the caller's argument was converted to the parameter's type, and that
conversion lands in the range, modulo 256 when the argument is outside it.
The range is an entry fact of the function, as a
`_Bool` parameter's `flag == 0 or flag == 1` is, so a claim may name the
parameter though the body never reads it.
`mdtests/a_uint8_parameter_claimed_below_its_range_at_entry_is_refused.md` and
`mdtests/an_int8_parameter_claimed_above_its_lower_bound_at_entry_is_refused.md`
are the negatives, and
`mdtests/a_wide_argument_to_a_narrow_parameter_wraps_into_its_range.md` is the
caller's side.

```c filename=a_narrow_parameter_has_its_type_range_at_entry.c
int32 ignore_u8(uint8 x) {
    return 0;
}

int32 ignore_u16(uint16 x) {
    return 0;
}

int32 ignore_i8(int8 x) {
    return 0;
}

int32 ignore_i16(int16 x) {
    return 0;
}
```

```click
verifying "a_narrow_parameter_has_its_type_range_at_entry.c";

int32 ignore_u8(uint8 x) {
    ensures x >= 0;
    ensures x <= 255;
} by { execute(); simp(); }

int32 ignore_u16(uint16 x) {
    ensures x >= 0;
    ensures x <= 65535;
} by { execute(); simp(); }

int32 ignore_i8(int8 x) {
    ensures x >= -128;
    ensures x <= 127;
} by { execute(); simp(); }

int32 ignore_i16(int16 x) {
    ensures x >= -32768;
    ensures x <= 32767;
} by { execute(); simp(); }
```

```expect
pass
```
