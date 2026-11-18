# Assembling a viewed C string at a call needs every body fact

The negative twin of
[`cstr_at_call_assembles_a_view_from_owned_bytes.md`](cstr_at_call_assembles_a_view_from_owned_bytes.md).
`measure` owns the bytes and states every fact of `cstr_at(src, n)` except
the terminator `src[n] == '\0'`. The bytes alone are not a C string of length
`n`, so the call cannot assemble the view its callee requires and is refused.
Assembling is a fold, so the refusal names the instance and the missing body
fact, as a refused `fold` does. The written terminator clause is accompanied
by its `p = src` and `len = n` call bindings.

```c filename=cstr_at_call_assembly_needs_the_terminator_fact.c
uint64 string_length(const uint8 *s, uint64 n);

uint64 measure(uint8 *src, uint64 n)
{
	return string_length(src, n);
}
```

```click
import click::c::string;

verifying "cstr_at_call_assembly_needs_the_terminator_fact.c";

extern uint64 string_length(const uint8* s, uint64 n) {
    views cstr_at(s, n);
    ensures result == n;
}

uint64 measure(uint8* src, uint64 n) {
    owns src[0..n + 1u64];
    requires n < 18446744073709551615u64;
    requires forall (k: uint64) { 0u64 <= k and k < n implies src[k] != '\0' };
    requires forall (k: uint64) { 0u64 <= k and k < n + 1u64 implies defined(src[k]) };
    ensures result == n;
}
```

```expect
fail: assembling `views cstr_at(src, n)` from the caller's bytes requires an exact body fact: missing pure fact: `p[len] == 0u8` (with p = src, len = n)
```
