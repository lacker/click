# A false claim about a converted integer constant is refused

The negative form of
`an_out_of_range_integer_constant_converts_modulo_its_destination_width.md`.
`unsigned char c = -56;` stores `200`, the value GCC gives it, so a claim
that the object keeps `-56` is refused.

```c filename=a_false_claim_about_a_converted_integer_constant_is_refused.c
int initialize(void) {
    unsigned char c = -56;
    return c;
}
```

```click
verifying "a_false_claim_about_a_converted_integer_constant_is_refused.c";

int initialize() { ensures result == -56 by auto; }
```

```expect
fail: unclosed goal
```
