# A C string folds at a constant length

A `fold` whose body fact is not available exactly leaves it to the fold's
implicit closer, spelled over the fold's arguments as written. A constant
argument is spelled as its literal, so `fold(cstr_at(p, 1u64))` proves its
quantified body facts from the caller's `requires` as `fold(cstr_at(p, n))`
does. Before, a constant argument had no spelling and the fold was refused at
the first quantified body fact, with a note that the available fact printed
identically. `empty` folds the empty string, whose nonzero-byte fact ranges
over no byte.

```c filename=cstr_at_folds_at_a_constant_length.c
int32 one(const uint8 *p) { return 0; }
int32 empty(const uint8 *p) { return 0; }
```

```click
import click::c::string;

verifying "cstr_at_folds_at_a_constant_length.c";

int32 one(const uint8* p) {
    consumes p[0..2u64];
    requires forall (k: uint64) { 0u64 <= k and k < 1u64 implies p[k] != '\0' };
    requires p[1u64] == '\0';
    requires forall (k: uint64) { 0u64 <= k and k < 1u64 + 1u64 implies defined(p[k]) };
    produces cstr_at(p, 1u64);
} by {
    have forall (k: uint64) { 0u64 <= k and to_integer(k) < to_integer(1u64 + 1u64) implies defined(p[k]) } by {
        intro(); intro();
        have 0u64 <= k and k < 1u64 + 1u64;
        instantiate(forall (j: uint64) { 0u64 <= j and j < 1u64 + 1u64 implies defined(p[j]) }, k);
        known();
    }
    fold(cstr_at(p, 1u64));
}

int32 empty(const uint8* p) {
    consumes p[0..1];
    requires p[0] == '\0';
    requires forall (k: uint64) { 0u64 <= k and k < 1u64 implies defined(p[k]) };
    produces cstr_at(p, 0u64);
} by {
    have forall (k: uint64) { 0u64 <= k and to_integer(k) < to_integer(0u64 + 1u64) implies defined(p[k]) } by {
        intro(); intro();
        instantiate(forall (j: uint64) { 0u64 <= j and j < 1u64 implies defined(p[j]) }, k);
        known();
    }
    fold(cstr_at(p, 0u64));
}
```

```expect
pass
```
