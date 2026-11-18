# A call map gives the length of a string a call assembles from owned bytes

`measure` owns the bytes of a C string of length `n` and states its facts,
but holds no `cstr_at` instance, so nothing held gives `string_length`'s
value parameter `n` a value. The call map gives it, `{ n: n }`, and the call
assembles the view `cstr_at(src, n)` from the owned bytes, as
[`cstr_at_call_assembles_a_view_from_owned_bytes.md`](cstr_at_call_assembles_a_view_from_owned_bytes.md)
does when the length is a C argument. `relay` passes on its own value
parameter, `{ n: n }`, the length of the string it was given.

```c filename=cstr_at_call_map_gives_the_length_of_a_string_a_call_assembles.c
uint64 string_length(const uint8 *s);

uint64 measure(uint8 *src, uint64 n)
{
	return string_length(src);
}

uint64 relay(const uint8 *src)
{
	return string_length(src);
}
```

```click
import click::c::string;

verifying "cstr_at_call_map_gives_the_length_of_a_string_a_call_assembles.c";

extern uint64 string_length(const uint8* s) {
    let n: uint64;
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
} by {
    step(string_length, { n: n });
}

uint64 relay(const uint8* src) {
    let n: uint64;
    views cstr_at(src, n);
    ensures result == n;
} by {
    step(string_length, { n: n });
}
```

```expect
pass
```
