# A call assembles a viewed C string from the bytes its caller owns

`measure` owns the bytes `src[0..n + 1]` and states the facts of a C string of
length `n` in its precondition, but holds no `cstr_at` instance. The callee
views `cstr_at(src, n)`, so the call assembles one: the owned bytes cover the
string's body piecewise, and its four facts hold at the call. The caller's
bytes are lent for the call and returned unchanged; no `cstr_at` persists in
the caller. The quantified facts are the caller's own statements, matched to
the body's up to the quantifier's name.
[`cstr_at_call_assembly_needs_the_terminator_fact.md`](cstr_at_call_assembly_needs_the_terminator_fact.md)
is the refusal when a fact is missing.

```c filename=cstr_at_call_assembles_a_view_from_owned_bytes.c
uint64 string_length(const uint8 *s, uint64 n);

uint64 measure(uint8 *src, uint64 n)
{
	return string_length(src, n);
}
```

```click
import click::c::string;

verifying "cstr_at_call_assembles_a_view_from_owned_bytes.c";

extern uint64 string_length(const uint8* s, uint64 n) {
    views cstr_at(s, n);
    ensures result == n;
}

uint64 measure(uint8* src, uint64 n) {
    owns src[0..n + 1u64];
    requires n < 18446744073709551615u64;
    requires forall (k: uint64) { 0u64 <= k and k < n implies src[k] != '\0' };
    requires src[n] == '\0';
    requires forall (k: uint64) { 0u64 <= k and to_integer(k) < to_integer(n + 1u64) implies defined(src[k]) };
    ensures result == n;
}
```

```expect
pass
```
