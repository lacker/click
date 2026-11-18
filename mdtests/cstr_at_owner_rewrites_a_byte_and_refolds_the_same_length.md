# An owner rewrites a byte of its C string and refolds the same length

`owns cstr_at(s, n)` holds the string's `n + 1` bytes exclusively and returns
the same instance, so the length is unchanged across the call. `poke` unfolds
the string, stores a nonzero byte inside it, restates the three memory facts
at the new state, and folds `cstr_at(s, n)` again. The terminator at `s[n]`
and every other byte carry over the store because `0 < n` places them apart
from `s[0]`.

```c filename=cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.c
void poke(uint8 *s, uint64 n) { s[0] = 'a'; }
```

```click
import click::c::string;

verifying "cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.c";

void poke(uint8* s, uint64 n) {
    owns cstr_at(s, n);
    requires 0u64 < n;
} by {
    unfold(cstr_at(s, n));
    step();
    have forall (k: uint64) { 0u64 <= k and k < n implies s[k] != '\0' } by {
        intro();
        intro();
        if k == 0u64 {
            rewrite(k, 0u64);
            solve();
        } else {
            instantiate(forall (k: uint64) { 0u64 <= k and k < n implies old(s[k]) != '\0' }, k);
            have separate(memory(s[k]), memory(s[0u64])) by {
                apply(click::separation::separate_elements(s, k, 0u64)) using { k != 0u64; };
            }
            have separate(statement(0).footprint, memory(s[k])) by {
                normalize() using { separate(memory(s[k]), memory(s[0u64])); };
            }
            have s[k] == old(s[k]) by {
                preserve(memory(s[k]), statement(0));
            }
            rewrite(s[k], old(s[k]));
            known();
        }
    }
    have n != 0u64 by { solve() using { 0u64 < n; }; }
    have separate(memory(s[n]), memory(s[0u64])) by {
        apply(click::separation::separate_elements(s, n, 0u64)) using { n != 0u64; };
    }
    have separate(statement(0).footprint, memory(s[n])) by {
        normalize() using { separate(memory(s[n]), memory(s[0u64])); };
    }
    have s[n] == old(s[n]) by {
        preserve(memory(s[n]), statement(0));
    }
    have s[n] == '\0' by { known(); }
    have forall (k: uint64) { 0u64 <= k and to_integer(k) < to_integer(n + 1u64) implies defined(s[k]) } by {
        intro();
        intro();
        if k == 0u64 {
            rewrite(k, 0u64);
            solve();
        } else {
            instantiate(forall (k: uint64) { 0u64 <= k and to_integer(k) < to_integer(n + 1u64) implies defined(old(s[k])) }, k);
            have separate(memory(s[k]), memory(s[0u64])) by {
                apply(click::separation::separate_elements(s, k, 0u64)) using { k != 0u64; };
            }
            have separate(statement(0).footprint, memory(s[k])) by {
                normalize() using { separate(memory(s[k]), memory(s[0u64])); };
            }
            preserve(memory(s[k]), statement(0));
        }
    }
    fold(cstr_at(s, n));
}
```

```expect
pass
```
