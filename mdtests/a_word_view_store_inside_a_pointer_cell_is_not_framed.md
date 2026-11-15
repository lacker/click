# a word store through a typed view is not framed away from the pointer it overwrites

The same store as `a_byte_store_inside_a_pointer_cell_is_not_framed.md`
without a byte view anywhere: an `int32*` view of an `int32**`, and an
ordinary four-byte store to element one of it. Element one of the `int32`
view is byte four of the pointer at `q`, which is its upper half on an LP64
target, so the pointer the next line reads back is not the pointer that was
there.

It was here because it reached the answer by a route the byte-view files do
not: both sides are pointer values, and the equality of their scaled
offsets was decided by comparing the two loads' origin states cell by
cell. An `int` store into an `int *` object is itself undefined (C11
6.5p7), and the strict-aliasing check now refuses the store before any goal
is reached. A word store into a pointer cell through a non-character type
always breaks that rule, so the route is unreachable; the byte-view files
keep covering the framing rule.

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
}
```

```expect
fail: an object of type `int *` accessed through an lvalue of type `int`
```
