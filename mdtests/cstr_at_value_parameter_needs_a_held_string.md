# A value parameter needs a string to take its length from

`measure` views the bytes of `src` but holds no `cstr_at` instance and
writes no call map, so nothing gives `string_length`'s `n` a value
and the call is refused with the parameter named.
[`cstr_at_call_map_gives_the_length_of_a_string_a_call_assembles.md`](cstr_at_call_map_gives_the_length_of_a_string_a_call_assembles.md)
gives the value in a call map instead.

```c filename=cstr_at_value_parameter_needs_a_held_string.c
uint64 string_length(const uint8 *s);

uint64 measure(const uint8 *src, uint64 n)
{
	return string_length(src);
}
```

```click
import click::c::string;

verifying "cstr_at_value_parameter_needs_a_held_string.c";

extern uint64 string_length(const uint8* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}

uint64 measure(const uint8* src, uint64 n) {
    views src[0..n + 1u64];
    ensures result == n;
}
```

```expect
fail: needs a held `cstr_at` instance to give `n` its value; the caller holds none that matches its other arguments; or give the value with `step(string_length, { n: value })`
```
