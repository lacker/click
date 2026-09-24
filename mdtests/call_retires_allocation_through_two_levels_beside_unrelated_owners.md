# A call retires a lent allocation through two levels beside unrelated owners

`box_teardown` calls `box_release`, which calls `box_destroy`, which frees
`box->data`. Each caller lends `boxed(box)` and keeps owned objects the
callee never sees: `object(other)` at both levels and `object(third)` at the
outer one. Each call rule reads the lent composite at its own entry, where
the lent `box->data[0..1]` covers the whole retired allocation, so the owned
objects each caller keeps are separate from it by the ownership partition
(`call_retires_allocation_beside_unrelated_owner.md`). The inner call's
retirement does not leak into the outer one: the outer rule sees only the
contract of `box_release`, and retires the allocation it lent.

```c filename=box.c
struct box {
    int32* data;
};

void box_destroy(struct box* box) {
    free(box->data);
}

void box_release(struct box* box, struct box* other) {
    box_destroy(box);
}

void box_teardown(struct box* box, struct box* other, struct box* third) {
    box_release(box, other);
}
```

```click
resource boxed(box: struct box*) {
    owns object(box);
    contains allocation(box->data, 4);
    owns box->data[0..1];
}

verifying "box.c";

void box_destroy(struct box* box) {
    consumes boxed(box);
    produces object(box);
} by {
    unfold(boxed(box));
    execute();
    simp();
}

void box_release(struct box* box, struct box* other) {
    consumes boxed(box);
    produces object(box);
    owns object(other);
} by {
    execute();
    simp();
}

void box_teardown(struct box* box, struct box* other, struct box* third) {
    consumes boxed(box);
    produces object(box);
    owns object(other);
    owns object(third);
} by {
    execute();
    simp();
}
```

```expect
pass
```
