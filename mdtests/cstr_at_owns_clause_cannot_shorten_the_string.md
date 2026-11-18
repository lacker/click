# An `owns` clause cannot shorten its C string

The length of `cstr_at(s, n)` is a parameter of the instance, and an `owns`
clause returns the instance it received. `cut` writes a terminator at `s[0]`
and folds the shorter string `cstr_at(s, 0)`, which is a different instance:
the exit holds `cstr_at(s, 0)` and the rest of the bytes, not the
`cstr_at(s, n)` its `owns` clause promises to return, so the proof is
refused. A function that changes the length consumes the old string and
produces the new one, as
[`cstr_at_consumes_and_produces_a_shorter_string.md`](cstr_at_consumes_and_produces_a_shorter_string.md)
does.

```c filename=cstr_at_owns_clause_cannot_shorten_the_string.c
void cut(uint8 *s, uint64 n) { s[0] = 0; }
```

```click
import click::c::string;

verifying "cstr_at_owns_clause_cannot_shorten_the_string.c";

void cut(uint8* s, uint64 n) {
    owns cstr_at(s, n);
    requires 0u64 < n;
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
fail: left `cut.owns_0` unproved
```
