# An owned open names the body fact its close cannot refold

An owner opens its C string and stores a nonzero byte inside it. The store
keeps the string valid, but the block states nothing about the new byte, so
the fold that closes `open` cannot re-establish the body's
`forall (k: uint64) { ... p[k] != '\0' }` at the new memory. The refusal
names that closing `fold` and the missing body fact, as an explicit `fold`
does; `cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.md` proves
the facts and refolds.

```c filename=cstr_at_owner_open_names_the_body_fact_left_at_close.c
void poke(uint8 *s, uint64 n) { s[0] = 'a'; }
```

```click
import click::c::string;
verifying "cstr_at_owner_open_names_the_body_fact_left_at_close.c";

void poke(uint8* s, uint64 n) {
    owns cstr_at(s, n);
    requires 0u64 < n;
} by {
    open(cstr_at(s, n)) {
        step_until(function.exit);
    }
}
```

```expect
fail: `fold(cstr_at(s, n))` requires an exact body fact
```
