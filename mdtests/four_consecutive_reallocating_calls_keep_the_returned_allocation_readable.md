# Four consecutive reallocating calls keep the returned allocation readable

The four-call form of
`consecutive_reallocating_calls_keep_the_returned_allocation_readable.md`,
with the value carried through all four `ensures` and the final read taken
without an explicit `unfold`.

```c filename=box.c
struct box {
    int32* data;
    int32 tag;
};

void box_renew(struct box* box) {
    int32* fresh;
    fresh = malloc(4);
    if (fresh == 0) {
        return;
    }
    fresh[0] = box->data[0];
    free(box->data);
    box->data = fresh;
}

int32 box_cycle(struct box* box) {
    box_renew(box);
    box_renew(box);
    box_renew(box);
    box_renew(box);
    return box->data[0];
}
```

```click
resource boxed(box: struct box*) {
    owns object(box);
    contains allocation(box->data, 4);
    owns box->data[0..1];
    fact separate(memory(object(box)), memory(box->data[0..1]));
}

verifying "box.c";

void box_renew(struct box* box) {
    consumes boxed(box);
    produces boxed(box);
    ensures box->data[0] == old(box->data[0]);
    ensures box->tag == old(box->tag);
} by {
    unfold(boxed(box));
    execute();
    simp();
}

int32 box_cycle(struct box* box) {
    consumes boxed(box);
    produces boxed(box);
    ensures result == old(box->data[0]);
} by {
    execute();
    simp();
}
```

```expect
pass
```
