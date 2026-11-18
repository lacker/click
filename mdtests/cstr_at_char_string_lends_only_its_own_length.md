# A borrowed character string is lent only at its own length

The negative twin of
[`cstr_at_borrows_a_char_string_from_the_library.md`](cstr_at_borrows_a_char_string_from_the_library.md).
`measure` borrows `cstr_at(src, n)` through a `char` pointer and calls a
callee that needs `cstr_at(src, n + 1)`. The byte view of the argument does
not loosen the match: the caller holds no string of that length, so the call
is refused.

```c filename=cstr_at_char_string_lends_only_its_own_length.c
uint64 string_length(const char *s, uint64 n);

uint64 measure(const char *src, uint64 n)
{
	return string_length(src, n + 1);
}
```

```click
import click::c::string;

verifying "cstr_at_char_string_lends_only_its_own_length.c";

extern uint64 string_length(const char* s, uint64 n) {
    views cstr_at(s, n);
    ensures result == n;
}

uint64 measure(const char* src, uint64 n) {
    views cstr_at(src, n);
    ensures result == n + 1u64;
}
```

```expect
fail: selected resource `views cstr_at(src, n + 1u64)`
```
