# A function that shortens a C string consumes it and produces the new one

`cut` writes a terminator at `s[0]`, so the string `cstr_at(s, n)` it was
given becomes the empty string `cstr_at(s, 0)`. The length is a parameter of
the instance, so the contract states the change: it consumes the old string
and produces the new one, with the bytes after the new terminator returned
as plain owned memory. The fold of `cstr_at(s, 0)` takes its one byte from the
front of the owned range `s[0..n + 1]` and leaves `s[1..n + 1]`. The `owns`
form of the same function is refused by
[`cstr_at_owns_clause_cannot_shorten_the_string.md`](cstr_at_owns_clause_cannot_shorten_the_string.md).

```c filename=cstr_at_consumes_and_produces_a_shorter_string.c
void cut(uint8 *s, uint64 n) { s[0] = 0; }
```

```click
import click::c::string;

verifying "cstr_at_consumes_and_produces_a_shorter_string.c";

void cut(uint8* s, uint64 n) {
    requires 0u64 < n;
    consumes cstr_at(s, n);
    produces cstr_at(s, 0u64);
    produces s[1u64..n + 1u64];
} by {
    unfold(cstr_at(s, n));
    step();
    have forall (k: uint64) { 0u64 <= k and k < 0u64 implies s[k] != '\0' } by {
        intro();
        intro();
        contradiction(false);
    }
    have s[0u64] == '\0' by {
        solve();
    }
    have forall (k: uint64) { 0u64 <= k and k < 0u64 + 1u64 implies defined(s[k]) } by {
        intro();
        intro();
        have k == 0u64 by {
            solve() using {
                k < 1u64;
            };
        }
        rewrite(k, 0u64);
        solve();
    }
    fold(cstr_at(s, 0u64));
}
```

```expect
pass
```
