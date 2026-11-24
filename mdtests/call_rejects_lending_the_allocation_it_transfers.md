# A caller cannot lend the allocation it transfers for freeing

The callee's owned allocation and borrowed view must come from separate
custody partitions. Passing `box->data` as both the owned allocation's contents
and the borrowed view is refused by call planning.

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

void aliased(struct box* box, struct box* other) {
    box_release(box, other, box->data);
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
}

void box_release(struct box* box, struct box* other, int32* q) {
    consumes boxed(box);
    produces *box;
    owns *other;
    views q[0..1];
} by {
    unfold(boxed(box));
    have separate(memory(((box->data as (void *)) as (uint8 *))[0..4]), memory(q[0..1])) by { close(); }
    fold(boxed(box));
    step() {
        requires separate(memory((box as (int32 *))[0..2]), memory((q as (int32 *))[0..1])) by { close(); }
        requires separate(memory(((box->data as (void *)) as (uint8 *))[0..4]), memory(q[0..1])) by { close(); }
    }
}
void aliased(struct box* box, struct box* other) {
    consumes boxed(box);
    produces *box;
    owns *other;
} by {
    observe(boxed(box));
}
```

```expect
fail:Borrowing this resource shape is unsupported.
```
