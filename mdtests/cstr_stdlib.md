# C-string standard library predicates

This checks the first C-string layer over `uint8[]`. These predicates are still
facts about C memory, not first-class Click string values:

- `cstr_len(p, len)` records an exact ghost length.
- `cstr_bounded(p, max)` records that a terminator exists before a bound.
- `cstr(p)` records that some exact ghost length exists for a plain pointer.

```c filename=cstr_stdlib.c
int32 cstr_stdlib(uint8 p[], int32 len, int32 max) {
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

int32 cstr_stdlib(uint8 p[], int32 len, int32 max) {
    requires loadable(p[0..len + 1]);
    requires loadable(p[0..max]);
    requires exact: cstr_len(p, len);
    requires bounded: cstr_bounded(p, max);

    ensures exact_length_nonnegative: 0 <= len by {
        execute();
        apply(cstr_len_nonnegative(p, len));
        simp();
    }

    ensures exact_prefix_has_no_null: cstr_prefix(p, len) by {
        execute();
        apply(cstr_len_has_prefix(p, len));
        simp();
    }

    ensures exact_has_terminator: bytes_contains(p, len, len + 1, '\0') by {
        execute();
        apply(cstr_len_has_terminator(p, len));
        simp();
    }

    ensures bounded_has_terminator: bytes_contains(p, 0, max, '\0') by {
        execute();
        unfold(cstr_bounded);
        simp();
    }
}

int32 plain_cstr(uint8 p[]) {
    requires input_is_cstr: cstr(p);

    ensures exposes_ghost_length: exists (int32 len) {
        cstr_len(p, len)
    } by {
        execute();
        unfold(cstr);
        choose(found_len from requirement input_is_cstr);
        witness(len = found_len);
        simp();
    }
}
```

```expect
pass
```
