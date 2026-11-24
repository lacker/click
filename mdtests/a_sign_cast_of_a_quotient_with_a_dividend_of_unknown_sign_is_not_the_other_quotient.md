# A sign cast of a quotient with a dividend of unknown sign is not the other quotient

The refusal beside
`a_sign_cast_of_a_nonnegative_quotient_is_the_quotient_at_the_other_signedness.md`:
rule C needs the dividend's `int32` reading known nonnegative. Here it is
not, and the two sides differ: for `n == 4294967295u` and `d == 2u`,
`(int)(n / d)` is `2147483647` while `(int)n / (int)d` is `-1 / 2`, `0`.

```c filename=a_sign_cast_of_a_quotient_with_a_dividend_of_unknown_sign_is_not_the_other_quotient.c
int unsigned_quotient_read_signed(unsigned n, unsigned d) {
    return (int)(n / d) == (int)n / (int)d;
}
```

```click
verifying "a_sign_cast_of_a_quotient_with_a_dividend_of_unknown_sign_is_not_the_other_quotient.c";

int unsigned_quotient_read_signed(uint32 n, uint32 d) {
    requires 0 < d as int32;
    ensures result == 1;
} by {
    have (d as int32) != 0 by close();
    have d != 0u32 by close();
    step_until(function.exit);
    close();
}
```

```expect
fail: `ensures result == 1` failed for `unsigned_quotient_read_signed.ensures_0`
```
