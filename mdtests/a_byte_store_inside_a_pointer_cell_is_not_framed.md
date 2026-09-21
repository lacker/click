# a byte store inside a pointer cell is not framed away from it

The pointer-valued companion of
`a_byte_store_inside_a_narrow_cell_is_not_framed.md`. A loaded pointer is
represented as its storage block at an offset scaled from the load, so its
equality is written as a pointer-offset equality rather than an integer one —
a different route to the same question, and one that was answering it from
cell maps just as the integer route was.

The store here is at byte four, which is the offset the address ladders like
best: it is a clean word away, the two pointers are unequal, their offsets
differ by a constant, and they are not the same element of any array. An LP64
pointer is eight bytes wide, so byte four is its upper half, and the read at
`q` returns it. Every offset from one to seven is covered by
`kernel::tests::memory_dag_tests::a_store_inside_a_read_refutes_the_load_equality_at_every_offset`.

The positive next door is `an_adjacent_wide_cell_survives_a_neighbouring_store.md`:
a whole-pointer element one element up is a clean eight bytes away and still
frames.

```c filename=a_byte_store_inside_a_pointer_cell_is_not_framed.c
int32* stale_pointer_read(int32** q) {
    unsigned char* b;
    b = (unsigned char*)(void*) q;
    b[4] = 7;
    return *q;
}
```

```click
verifying "a_byte_store_inside_a_pointer_cell_is_not_framed.c";

int32* stale_pointer_read(int32** q) {
    owns q[0..1];
    ensures result == old(q[0]);
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal: result == old(q[0]); the two sides read the same address in different memory snapshots (`result` reads the outcome state, `old(q[0])` reads function entry)
```
