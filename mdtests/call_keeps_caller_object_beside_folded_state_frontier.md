# Frontier: a call through a folded state havocs the caller's other objects

`keep_box` owns a folded field-free `cells` resource and a separate
`object(b)`. It stores `5` in `b->v`, lends the state to `touch`, which owns
`cells` for the call, and returns `b->v`. The callee holds only `cells`, and
a store needs ownership, so it cannot write `b->v`: the caller keeps
`object(b)` outside the transfer, and the partition at the call keeps it
apart from anything the callee can come to hold. `ensures result == 5` is
true.

The call rule does not use that partition. The havoc it applies is the
callee's footprint, the ranges `cells` expands to, and it keeps a caller cell
only when a fact proves the cell apart from those ranges. With `flags[0..n]`
and `data[0..n]` owned directly beside `object(b)`, the caller's composition
separates them member from member, and the same function verifies
(`mdtests/call_keeps_caller_object_beside_flat_ranges.md`). Folded inside
`cells` they are one member whose ranges the separation query cannot see, so
`b->v` is dropped. An iterated clause, whose footprint is the span of every
element it could hold, only widens what is lost.

This is the gap that blocks the per-cell arena pipeline in
`examples/arena`: every call there passes the folded `arena_state`, whose
footprint spans the whole data buffer, and the caller loses its region
descriptors and the values written through the other regions. The intended
fix is the call counterpart of
`mdtests/loop_keeps_cells_the_function_keeps_owning.md`: the call havoc, its
structural checker, and the memory-DAG hop across the call keep a cell that
the caller's residual resources hold, opening a residual field-bearing
instance one body layer so a region descriptor and its data range count.

```c filename=call_frontier_caller_object_beside_folded_state.c
struct box {
    int32 v;
};

void touch(int32* flags, int32* data, int32 n) {
    return;
}

int32 keep_box(int32* flags, int32* data, int32 n, struct box* b) {
    b->v = 5;
    touch(flags, data, n);
    return b->v;
}
```

```click
resource cells(flags: int32*, data: int32*, n: int32) {
    owns flags[0..n];
    owns data[0..n];
}

verifying "call_frontier_caller_object_beside_folded_state.c";

void touch(int32* flags, int32* data, int32 n) {
    owns cells(flags, data, n);
} by {
    execute();
    simp();
}

int32 keep_box(int32* flags, int32* data, int32 n, struct box* b) {
    owns cells(flags, data, n);
    owns object(b);
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == 5` failed
```
