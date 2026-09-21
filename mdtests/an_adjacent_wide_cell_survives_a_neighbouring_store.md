# the next eight-byte element survives a store to this one

The positive companion of `a_byte_store_inside_a_wide_cell_is_not_framed.md`.
Deciding separation by bytes rather than by address alone must not cost the
ordinary case anything: an eight-byte store at `q[1]` starts exactly where
the eight-byte cell at `q[0]` ends, so the two byte ranges are disjoint and
the read is framed across the store with no premise stated for it.

This is the boundary the refusals sit next to. Move the store one byte lower
and it would overlap; here the gap is exactly the access width, which is
enough.

```c filename=an_adjacent_wide_cell_survives_a_neighbouring_store.c
int64 keep_first(int64* q) {
    q[1] = 7;
    return q[0];
}
```

```click
verifying "an_adjacent_wide_cell_survives_a_neighbouring_store.c";

int64 keep_first(int64* q) {
    owns q[0..2];
    ensures result == old(q[0]);
} by {
    execute();
    simp();
}
```

```expect
pass
```
