# A call does not keep a cell of a residual instance it cannot open

`keep_box` keeps `maybe_box(b)` outside the call while it lends `cells`.
Both arms the premises leave possible own `object(b)`, so `b->v` is readable
and the claim is true, but the arm is not decided. The call havoc keeps a
cell an owned residual member holds only when it can read the member's body
exactly, and it opens only an unconditional, unmatched instance body one
layer: a matched body (decided or not), a guarded or witness-bearing one
keeps nothing. So `b->v` is havocked: the rule keeps only bytes it reads
exactly.

```c filename=call_havocs_cell_of_unopened_residual_instance.c
struct box {
    int32 v;
};

void touch(int32* flags, int32* data, int32 n) {
    return;
}

void keep_box(int32* flags, int32* data, int32 n, struct box* b) {
    touch(flags, data, n);
}
```

```click
spec enum Slot {
    Gone,
    Empty,
    Full,
}

resource maybe_box(b: struct box*) {
    field model: Slot;
    match model {
        Slot::Gone => {},
        Slot::Empty => {
            owns object(b);
        },
        Slot::Full => {
            owns object(b);
        },
    }
}

resource cells(flags: int32*, data: int32*, n: int32) {
    owns flags[0..n];
    owns data[0..n];
}

verifying "call_havocs_cell_of_unopened_residual_instance.c";

void touch(int32* flags, int32* data, int32 n) {
    owns cells(flags, data, n);
} by {
    execute();
    simp();
}

void keep_box(int32* flags, int32* data, int32 n, struct box* b) {
    owns cells(flags, data, n);
    owns m: maybe_box(b);
    requires m.model != Slot::Gone;
    requires b->v == 5;
    ensures b->v == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures b->v == 5` failed
```
