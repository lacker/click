# A call frees an owned allocation beside a separately borrowed view

`boxed(box)` owns every byte of the allocation that `box_destroy` frees.
The caller's `views q[0..1]` is backed by a separate checked loan, so it cannot
alias those owned bytes in a valid entry partition. Opening the composite
carries that separation to the retirement check without a written premise.
`call_rejects_lending_the_allocation_it_transfers.md` rejects a caller that
tries to supply the freed cell itself as this borrowed view.

```c filename=box.c
struct box {
    int32* data;
};

void box_destroy(struct box* box) {
    free(box->data);
}

void box_release(struct box* box, struct box* other, int32* q) {
    box_destroy(box);
}
```

```click
resource boxed(box: struct box*) {
    owns *box;
    owns allocation(box->data, 4);
    owns box->data[0..1];
}

verifying "box.c";

void box_destroy(struct box* box) {
    consumes boxed(box);
    produces *box;
} by {
    unfold(boxed(box));
    execute();
    simp();
}

void box_release(struct box* box, struct box* other, int32* q) {
    consumes boxed(box);
    produces *box;
    owns *other;
    views q[0..1];
} by {
    execute();
    simp();
}
```

```expect
pass
```
