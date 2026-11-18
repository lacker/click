# A value parameter does not choose between two held strings

`measure` views the same bytes as two strings, `cstr_at(src, n)` and
`cstr_at(src, m)`. Their facts make `n` and `m` equal, but the call does not
search for that: two held instances agree with the clause's pointer, so the
call cannot choose `string_length`'s `n` and is refused. A call map such
as `{ n: n }` gives the value to use.

```c filename=cstr_at_value_parameter_refuses_an_ambiguous_choice.c
uint64 string_length(const uint8 *s);

uint64 measure(const uint8 *src, uint64 n, uint64 m)
{
	return string_length(src);
}
```

```click
import click::c::string;

verifying "cstr_at_value_parameter_refuses_an_ambiguous_choice.c";

extern uint64 string_length(const uint8* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}

uint64 measure(const uint8* src, uint64 n, uint64 m) {
    views cstr_at(src, n);
    views cstr_at(src, m);
    ensures result == n;
}
```

```expect
fail: cannot choose `n`
```
