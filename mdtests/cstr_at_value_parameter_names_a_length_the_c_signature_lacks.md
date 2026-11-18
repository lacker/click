# A value parameter names the length of a C string its signature does not carry

`string_length` takes only the pointer. Its contract declares the string's
length as a value parameter, `let n: uint64;`, views `cstr_at(s, n)`, and
names `n` in its postcondition. The callee is specified for every length,
and each call takes the length from the string its caller holds. `measure`
holds `views cstr_at(src, n)`, so the call to `string_length(src)` takes `n`
and returns it, without the length passing through C.

```c filename=cstr_at_value_parameter_names_a_length_the_c_signature_lacks.c
uint64 string_length(const uint8 *s);

uint64 measure(const uint8 *src, uint64 n)
{
	return string_length(src);
}
```

```click
import click::c::string;

verifying "cstr_at_value_parameter_names_a_length_the_c_signature_lacks.c";

extern uint64 string_length(const uint8* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}

uint64 measure(const uint8* src, uint64 n) {
    views cstr_at(src, n);
    ensures result == n;
}
```

```expect
pass
```
