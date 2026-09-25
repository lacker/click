# A call keeps a caller object beside a folded state it lends

`keep_box` owns a folded field-free `cells` resource and a separate
`object(b)`. It stores `5` in `b->v`, lends the state to `touch`, which owns
`cells` for the call, and returns `b->v`. `ensures result == 5` verifies.

The havoc a call applies is the callee's footprint, here the ranges `cells`
expands to, and the separation query cannot see those ranges apart from
`b->v` while they are folded inside one member. It used to keep a caller
cell only when a fact proved it apart from the footprint, so `b->v` was
dropped. The callee holds only `cells`, though, and a store needs
ownership: the caller keeps `object(b)` outside the transfer, and at the
call the transferred and residual resources are one valid composition, so
the bytes `object(b)` holds are disjoint from everything the callee can own.
The call havoc now keeps a cell an owned member of the caller's residual
context holds. With `flags[0..n]` and `data[0..n]` owned directly the same
function always verified
(`mdtests/call_keeps_caller_object_beside_flat_ranges.md`).

```c filename=call_keeps_caller_object_beside_folded_state.c
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

verifying "call_keeps_caller_object_beside_folded_state.c";

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
pass
```
