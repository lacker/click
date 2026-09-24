# Frontier: a call that frees a lent allocation beside an unrelated owner

This fixture pins an open gap in the call rule met while verifying
`examples/arena`'s `arena_pipeline`, whose every path ends in
`arena_destroy(arena)` while the caller still owns its region descriptors.

`box_release` lends `boxed(box)`, which packages the allocation authority for
`box->data` together with the whole allocated cell, to `box_destroy`, which
frees it. The caller also owns `object(other)`. Before the call the caller's
ownership partition makes `other` disjoint from every byte of the allocation,
because the lent composite owns all of them. The call rule does not use that:
when the callee retires an allocation whose pointer is a symbolic external
value, it asks for an explicit separation fact between each resource the
caller keeps and the retired allocation, in exactly the kernel's spelling, and
refuses the call when it finds none. In the arena pipeline, written
`have separate(memory(...), memory(...))` facts between each descriptor and
each backing range did not satisfy it either: the check looks for the exact
allocation range the kernel derives from the allocation's byte count.

The intended behavior is that a caller-kept owned resource is known separate
from an allocation the call retires whenever the lent resources owned the
allocation's complete memory at the call, so this fixture should pass.

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
    step();
    simp();
}
```

```expect
fail: resource would remain usable after its allocation is freed
```
