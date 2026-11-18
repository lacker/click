# A borrowed C string passes through a call

`views cstr_at(src, n)` borrows the `n + 1` bytes of `src` through its
terminator; `cstr_at` is declared in the `click::c::string` library module.
`measure` receives that loan and lends the same composite to `string_length`
without opening it: the call needs no unfold, refold, or restatement of the
string's facts. `string_length` stands for a library
function whose contract takes the borrowed string; its length is a C argument
here only because a contract cannot yet name a length its C signature does
not carry.

```c filename=cstr_at_view_passes_through_a_call.c
uint64 string_length(const uint8 *s, uint64 n);

uint64 measure(const uint8 *src, uint64 n)
{
	return string_length(src, n);
}
```

```click
import click::c::string::{cstr_at};

verifying "cstr_at_view_passes_through_a_call.c";

extern uint64 string_length(const uint8* s, uint64 n) {
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
