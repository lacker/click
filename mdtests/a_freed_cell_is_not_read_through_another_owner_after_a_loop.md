# A freed cell is not read through another owner after a loop

A use after free. `f` saves `h->ptr`, a loop swaps the pointers of two
holders once, `f` frees `g->ptr`, which is now the saved pointer, and then
reads through `saved`.

The loop records which holder points to `saved` before and after the swap.
Its proof preserves `h->ptr` through the write to `g->ptr` so it can rebuild
both owners. At the free, `g->ptr == saved` identifies the allocation being
released. The verifier then rejects the read through `saved`.

```c filename=a_freed_cell_is_not_read_through_another_owner_after_a_loop.c
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
    free(g->ptr);
    return saved[0];
}
```

```click
resource holder(h: struct holder*) {
    owns h->ptr;
    owns allocation(h->ptr, 4);
    owns h->ptr[0..1];
}

verifying "a_freed_cell_is_not_read_through_another_owner_after_a_loop.c";

int32 f(struct holder* h, struct holder* g) {
    owns holder(h);
    consumes holder(g);
    produces g->ptr;
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    loop {
        decreases 1 - i;
        invariant 0 <= i and i <= 1;
        invariant i == 0 implies h->ptr == saved;
        invariant i == 1 implies g->ptr == saved;
        owns holder(h);
        owns holder(g);
        initialize by close();
        maintain by {
            unfold(holder(h));
            unfold(holder(g));
            have i == 0 by close();
            have h->ptr == saved by close();
            step();
            have t == saved by close();
            mark before_first_store;
            have separate(memory(h->ptr), memory(g->ptr)) by close();
            step();
            have h->ptr == at(before_first_store, g->ptr) by close();
            mark before_second_store;
            step();
            have separate(loop(0).statement(2).footprint, memory(h->ptr)) by {
                normalize() using { separate(memory(h->ptr), memory(g->ptr)); };
            }
            have h->ptr == at(before_second_store, h->ptr) by {
                preserve(memory(h->ptr), loop(0).statement(2));
            }
            fold(holder(h));
            have g->ptr == saved by close();
            fold(holder(g));
            step();
            have i == 1 by close();
            have g->ptr == saved by close();
            close();
        }
    }
    unfold(holder(g));
    have i == 1 by close();
    have g->ptr == saved by close();
    step();
    step();
    close();
}
```

```expect
fail: invalid memory access
```
