# An out-of-range return narrowing wraps modulo 256

Returning an `int32` from a `uint8` function converts it modulo 256, as GCC
and Clang do, and owes no range. With `x == 300` the result is 44. The
published path and its checked trace agree on that value.
`mdtests/a_return_narrowing_in_range_verifies.md` is the in-range case, and
`mdtests/a_false_claim_about_a_wrapped_value_is_refused.md` refuses claiming
the unconverted value.

```c filename=an_out_of_range_return_narrowing_wraps_modulo_256.c
uint8 f(int32 x) { return x; }
```

```click
verifying "an_out_of_range_return_narrowing_wraps_modulo_256.c";

uint8 f(int32 x) {
    requires x == 300;
    ensures result == 44;
} by { execute(); simp(); }
```

```expect
pass
```
