# C-string standard library predicates

This checks the first C-string layer over `uint8[]`. These predicates are still
facts about C memory, not first-class Click string values:

- `string::len(p, len)` records an exact ghost length.
- `string::bounded(p, max)` records that a terminator exists before a bound.
- `string::cstr(p)` records that some exact ghost length exists for a plain pointer.

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
import click::c::string;

verifying "cstr_stdlib.c";
verifying "plain_cstr.c";

int32 cstr_stdlib(uint8 p[], uint64 len, uint64 max) {
    requires viewable(p[0..len + 1u64]);
    requires viewable(p[0..max]);
    requires string::len(p, len);
    requires string::bounded(p, max);

    ensures exact_prefix_has_no_null: string::prefix(p, len) by {
        step_until(function.exit);
        apply(string::len_has_prefix(p, len));
        close();
    }

    ensures exact_has_terminator: p[len] == '\0' by {
        step_until(function.exit);
        apply(string::len_has_terminator(p, len));
        close();
    }

    ensures bounded_has_terminator: exists (k: uint64) { k < max and p[k] == '\0' } by {
        step_until(function.exit);
        unfold(string::bounded(p, max));
        close();
    }
}

int32 plain_cstr(uint8 p[]) {
    requires string::cstr(p);

    ensures exposes_ghost_length: exists (len: uint64) {
        string::len(p, len)
    } by {
        step_until(function.exit);
        unfold(string::cstr(p));
        let found_len = obtain(at(function.entry, exists (found_len: uint64) { string::len(p, found_len) }));
        witness(found_len);
        close();
    }
}
```

```expect
pass
```
