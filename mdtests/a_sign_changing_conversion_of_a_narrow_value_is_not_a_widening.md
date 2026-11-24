# A sign-changing conversion of a narrow value is not a widening

A negative of
[`solve_widens_a_narrow_value_into_a_containing_type.md`](solve_widens_a_narrow_value_into_a_containing_type.md).
`unsigned int` does not contain `signed char`: converting `-1` gives
`4294967295`, so the result is not read as the same value.

```c filename=sign_change.c
unsigned int sign_change(signed char x) { return x; }
```

```click
verifying "sign_change.c";

unsigned int sign_change(signed char x) {
    ensures to_integer(result) == to_integer(x);
} by { step_until(function.exit); close(); }
```

```expect
fail: did not retain a complete proof for `sign_change.ensures_0`
```
