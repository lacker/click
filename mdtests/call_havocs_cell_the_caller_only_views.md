# A call does not keep a cell its caller only views

The negative of `call_keeps_caller_object_beside_folded_state.md`: the
caller holds `b->v` only as a view. A view's owner may be anywhere, including
inside the `cells` the caller lends, so the callee may own and write the
cell, and the call havoc must drop it. Only an owned member of the caller's
residual resources keeps a cell across a call.

```c filename=call_havocs_cell_the_caller_only_views.c
struct box {
    int32 v;
};

void touch(int32* flags, int32* data, int32 n) {
    return;
}

int32 keep_box(int32* flags, int32* data, int32 n, struct box* b) {
    touch(flags, data, n);
    return b->v;
}
```

```click
resource cells(flags: int32*, data: int32*, n: int32) {
    owns flags[0..n];
    owns data[0..n];
}

verifying "call_havocs_cell_the_caller_only_views.c";

void touch(int32* flags, int32* data, int32 n) {
    owns cells(flags, data, n);
} by {
    execute();
    simp();
}

int32 keep_box(int32* flags, int32* data, int32 n, struct box* b) {
    owns cells(flags, data, n);
    views b->v;
    requires b->v == 5;
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == 5` failed
```
