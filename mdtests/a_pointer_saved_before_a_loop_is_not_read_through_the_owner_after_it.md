# A pointer saved before a loop is not read through the owner after it

`holder(h)` owns the cell `h->ptr` points at, an address its definition
reads out of memory. `f` saves `h->ptr`, then a loop swaps the pointers of
two holders, and `f` reads through the saved pointer with both holders
folded.

Before the loop, holding `holder(h)` lets C read `saved[0]`: it is the cell
the holder owns. After the loop it is not known to be: the loop may have
moved that cell to `holder(g)`. The read authority a holder gives is derived
again at the loop head over the memory an arbitrary visit sees, so it covers
the cell `h->ptr` points at then, and the read through `saved` is refused.

The read would in fact be safe here, since one of the two holders owns the
cell. `a_freed_cell_is_not_read_through_another_owner_after_a_loop.md` is the
same loop where it is not.

```c filename=stale.c
struct holder {
    int32* ptr;
};

int32 f(struct holder* h, struct holder* g) {
    int32* saved = h->ptr;
    int32* t = 0;
    int32 i = 0;
    while (i < 1) {
        t = h->ptr;
        h->ptr = g->ptr;
        g->ptr = t;
        i = i + 1;
    }
    return saved[0];
}
```

```click
resource holder(h: struct holder*) {
    owns h->ptr;
    owns allocation(h->ptr, 4);
    owns h->ptr[0..1];
}

verifying "stale.c";

int32 f(struct holder* h, struct holder* g) {
    owns holder(h);
    owns holder(g);
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    loop {
        decreases 1 - i;
        invariant i >= 0;
        owns holder(h);
        owns holder(g);
        initialize by close();
        maintain by {
            unfold(holder(h));
            unfold(holder(g));
            step(); step(); step(); step();
            fold(holder(h));
            fold(holder(g));
        }
    }
    step();
    close();
}
```

```expect
fail: missing resource fact
```
