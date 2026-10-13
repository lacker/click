# C-string standard library predicates

This checks the first C-string layer over `uint8[]`. These predicates are still
facts about C memory, not first-class Click string values:

- `cstr_len(p, len)` records an exact ghost length.
- `cstr_bounded(p, max)` records that a terminator exists before a bound.
- `cstr(p)` records that some exact ghost length exists for a plain pointer.

Lengths and bounds are `size_t` values, as C measures them.

```c filename=cstr_stdlib.c
int32 cstr_stdlib(uint8 p[], uint64 len, uint64 max) {
    return 0;
}
```

```c filename=plain_cstr.c
int32 plain_cstr(uint8 p[]) {
    return 0;
}
```

```click
verifying "cstr_stdlib.c";
verifying "plain_cstr.c";

int32 cstr_stdlib(uint8 p[], uint64 len, uint64 max) {
    requires viewable(p[0..len + 1u64]);
    requires viewable(p[0..max]);
    requires cstr_len(p, len);
    requires cstr_bounded(p, max);

    ensures exact_prefix_has_no_null: cstr_prefix(p, len) by {
        execute();
        apply(cstr_len_has_prefix(p, len));
        simp();
    }

    ensures exact_has_terminator: p[len] == '\0' by {
        execute();
        apply(cstr_len_has_terminator(p, len));
        simp();
    }

    ensures bounded_has_terminator: exists (k: uint64) { k < max and p[k] == '\0' } by {
        execute();
        unfold(cstr_bounded);
        simp();
    }
}

int32 plain_cstr(uint8 p[]) {
    requires cstr(p);

    ensures exposes_ghost_length: exists (len: uint64) {
        cstr_len(p, len)
    } by {
        execute();
        unfold(cstr);
        obtain (found_len: uint64) {
            at(function.entry, cstr_len(p, found_len))
        }
        witness { len: found_len };
        simp();
    }
}
```

```expect
pass
```
