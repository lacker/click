# a store inside a cell is not separated from it by its address

A store one byte into an eight-byte cell is at a *different address* from the
cell, and every address test there is agrees: the two pointers are not equal,
their offsets differ by a constant, they are not the same element of any
array. None of that is the question. The question is whether the store wrote
any of the bytes this load reads, and a one-byte store at `q + 1` writes the
second byte of the `int64` at `q`.

The address ladders that separate a load from a store may therefore only
stand in for the byte question where the gap they establish clears the
access. Here there is a constant gap of one byte and an eight-byte read, so
the bytes overlap outright and no ladder may speak: the store affected the
cell, and the diagnostic says which store and which cell.

`byte_store_at_offset_4_is_not_framed.md` is the same store on the word
boundary, and `an_adjacent_wide_cell_survives_a_neighbouring_store.md` is the
companion where the gap really does clear the access. Every offset from one to
seven is covered without a byte view at all by
`kernel::resource_tracker::tests::a_narrow_store_inside_a_wide_cell_reports_changed`.

A note on the C: a `unsigned char` view reached through `void*` is accepted as
a conversion (`byte_representation_untyped_source_frontier.md` passes one to
`memcpy`), while the one-step retyping cast `(unsigned char*) q` is refused
outright. Storing *through* such a view, as this file does, is on the frontier
between the two, and what is pinned here is the byte-overlap rule it runs
into, not an endorsement of the cast. If the frontier is later tightened to
refuse this store, the kernel test above keeps the rule covered and this file
should follow the frontier.

```c filename=a_byte_store_inside_a_wide_cell_is_not_framed.c
int64 stale_wide_read(int64* q) {
    unsigned char* b;
    b = (unsigned char*)(void*) q;
    b[1] = 7;
    return *q;
}
```

```click
verifying "a_byte_store_inside_a_wide_cell_is_not_framed.c";

int64 stale_wide_read(int64* q) {
    owns q[0..1];
    ensures result == old(q[0]);
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal: result == old(q[0]); the two sides read the same address in different memory snapshots (`result` reads the outcome state, `old(q[0])` reads function entry); `q[0]` changed since function entry: the store to `q[…]` wrote it. The one later step does not touch it.
```
