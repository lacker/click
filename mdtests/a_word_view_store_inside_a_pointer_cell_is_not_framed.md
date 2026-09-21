# a word store through a typed view is not framed away from the pointer it overwrites

The same store as `a_byte_store_inside_a_pointer_cell_is_not_framed.md`
without a byte view anywhere: an `int32*` view of an `int32**`, and an
ordinary four-byte store to element one of it. Element one of the `int32`
view is byte four of the pointer at `q`, which is its upper half on an LP64
target, so the pointer the next line reads back is not the pointer that was
there.

It is here because it reached the answer by a route the byte-view files do
not. Both sides are pointer values, so the goal is a pointer-offset equality;
the offsets are loads scaled by the element width, and the equality of *those*
was decided by comparing the two loads' origin snapshots cell by cell. That
comparison is now vetoed by the recorded history like the others, so the one
rule answers a goal written three different ways.

```c filename=a_word_view_store_inside_a_pointer_cell_is_not_framed.c
int32* stale_pointer_read(int32** q) {
    int32* w;
    w = (int32*)(void*) q;
    w[1] = 7;
    return *q;
}
```

```click
verifying "a_word_view_store_inside_a_pointer_cell_is_not_framed.c";

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
