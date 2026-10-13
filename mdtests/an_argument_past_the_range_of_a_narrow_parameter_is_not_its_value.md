# An argument past the range of a narrow parameter is not its value

With `y` known only to be in `0..300`, its conversion to `widen`'s `uint8`
parameter wraps 256 through 300 to 0 through 44, so `widen(y) == y` is not
proved. The in-range companion is
`mdtests/an_in_range_argument_to_a_narrow_parameter_is_its_value_at_the_caller.md`.

```c filename=an_argument_past_the_range_of_a_narrow_parameter_is_not_its_value.c
int32 widen(uint8 x) { return x; }
int32 pass_wide(int32 y) { return widen(y); }
```

```click
verifying "an_argument_past_the_range_of_a_narrow_parameter_is_not_its_value.c";

int32 widen(uint8 x) {
    ensures result == x;
} by { execute(); simp(); }

int32 pass_wide(int32 y) {
    requires 0 <= y;
    requires y <= 300;
    ensures result == y;
} by { execute(); simp(); }
```

```expect
fail: `ensures result == y` failed for `pass_wide.ensures_0`
```
