# A call map cannot give a length the caller holds no string for

`measure` holds `cstr_at(src, n)` and gives `string_length`'s `n` the value
`n + 1` in its call map. A call map grants nothing: the call still requires
`views cstr_at(src, n + 1)`, which the caller neither holds nor can assemble,
so it is refused.

```c filename=cstr_at_call_map_refuses_a_length_the_caller_holds_no_string_for.c
uint64 string_length(const uint8 *s);

uint64 measure(const uint8 *src, uint64 n)
{
	return string_length(src);
}
```

```click
import click::c::string;

verifying "cstr_at_call_map_refuses_a_length_the_caller_holds_no_string_for.c";

extern uint64 string_length(const uint8* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}

uint64 measure(const uint8* src, uint64 n) {
    views cstr_at(src, n);
    requires n < 1000u64;
    ensures result == n + 1u64;
} by {
    step(string_length, { n: n + 1u64 });
}
```

```expect
fail: views cstr_at(src, n + 1u64)
```
