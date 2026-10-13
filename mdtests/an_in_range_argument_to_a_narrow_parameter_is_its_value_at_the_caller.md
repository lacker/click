# An in-range argument to a narrow parameter is its value at the caller

`widen`'s guarantee names its `uint8` parameter, so at the caller it names
the argument's conversion to `uint8`. Where the caller already knows the
argument is in `0..255`, by range facts or by a constant, the conversion is
the argument (`narrowed_cast_identity`), and the guarantee proves
`result == y`. `mdtests/an_argument_past_the_range_of_a_narrow_parameter_is_not_its_value.md`
is the negative.

```c filename=an_in_range_argument_to_a_narrow_parameter_is_its_value_at_the_caller.c
int32 widen(uint8 x) { return x; }
int32 pass_range(int32 y) { return widen(y); }
int32 pass_known(int32 y) { return widen(y); }
```

```click
verifying "an_in_range_argument_to_a_narrow_parameter_is_its_value_at_the_caller.c";

int32 widen(uint8 x) {
    ensures result == x;
} by { execute(); simp(); }

int32 pass_range(int32 y) {
    requires 0 <= y;
    requires y <= 255;
    ensures result == y;
} by { execute(); simp(); }

int32 pass_known(int32 y) {
    requires y == 44;
    ensures result == 44;
    ensures result == y;
} by { execute(); simp(); }
```

```expect
pass
```
