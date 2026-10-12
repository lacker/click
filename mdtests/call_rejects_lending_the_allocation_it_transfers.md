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
void aliased(struct box* box, struct box* other) {
    consumes boxed(box);
    produces *box;
    owns *other;
} by {
    observe(boxed(box));
    execute();
    simp();
}
```

```expect
fail:stable-view this resource shape is outside stable-view support refused during planning
```
