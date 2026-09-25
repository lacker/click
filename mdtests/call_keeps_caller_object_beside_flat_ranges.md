# A call keeps a caller object its flat ranges are separate from

The control for `call_keeps_caller_object_beside_folded_state_frontier.md`.
The caller owns `flags[0..n]`, `data[0..n]`, and `object(b)` directly and
lends the two ranges to `touch`. Its composition holds each as its own
member, so the call's havoc keeps `b->v` and `result == 5` verifies.

```c filename=call_keeps_caller_cell_flat.c
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

verifying "call_keeps_caller_cell_flat.c";

void touch(int32* flags, int32* data, int32 n) {
    owns flags[0..n];
    owns data[0..n];
} by {
    execute();
    simp();
}

int32 keep_box(int32* flags, int32* data, int32 n, struct box* b) {
    owns flags[0..n];
    owns data[0..n];
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
