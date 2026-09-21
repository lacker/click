# a byte store inside an `int32` is not framed away from it

The narrow companion of `a_byte_store_inside_a_wide_cell_is_not_framed.md`.
That one reads an `int64`, whose equality had no memory-resolution rule at
all, so it was refused for a reason that had nothing to do with bytes. This
one reads an `int32`, whose equality every framing route does decide, and it
was **provable** until those routes were made to ask the recorded history.

What made the addresses beside the point a second time is that by the time
the two reads are compared, neither snapshot still *holds* the write. The
comparisons that decided this read cell maps, and a cell map records what is
known at a point rather than what happened to it: the store drops the `int32`
cell it partly overwrites, and the naming projection discards the byte cell it
leaves behind. Two snapshots a store separates were therefore cell-identical,
and the absence of a differing cell was read as "nothing differs". The store
is in the recorded history either way, which is what is now asked.

Every offset from one to three, in this cell and in a pointer-valued one, is
covered without a byte view at all by
`kernel::tests::memory_dag_tests::a_store_inside_a_read_refutes_the_load_equality_at_every_offset`.

The note on the C in `a_byte_store_inside_a_wide_cell_is_not_framed.md`
applies here too: what is pinned is the byte-overlap rule this store runs
into, not an endorsement of the byte view.

```c filename=a_byte_store_inside_a_narrow_cell_is_not_framed.c
int32 stale_narrow_read(int32* q) {
    unsigned char* b;
    b = (unsigned char*)(void*) q;
    b[1] = 7;
    return *q;
}
```

```click
verifying "a_byte_store_inside_a_narrow_cell_is_not_framed.c";

int32 stale_narrow_read(int32* q) {
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
