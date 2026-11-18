# A caller cannot claim a different length than the call takes

The negative twin of
[`cstr_at_value_parameter_names_a_length_the_c_signature_lacks.md`](cstr_at_value_parameter_names_a_length_the_c_signature_lacks.md).
The call takes `string_length`'s `n` from the string `measure` holds,
`cstr_at(src, n)`, so the result is `n`; the claim that it is `n + 1` is
refused.

```c filename=cstr_at_value_parameter_refuses_a_wrong_length_claim.c
uint64 string_length(const uint8 *s);

uint64 measure(const uint8 *src, uint64 n)
{
	return string_length(src);
}
```

```click
import click::c::string;

verifying "cstr_at_value_parameter_refuses_a_wrong_length_claim.c";

extern uint64 string_length(const uint8* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}

uint64 measure(const uint8* src, uint64 n) {
    views cstr_at(src, n);
    requires n < 1000u64;
    ensures result == n + 1u64;
}
```

```expect
fail: unclosed goal: to_integer(result) == (to_integer(n) + to_integer(1u64))
```
