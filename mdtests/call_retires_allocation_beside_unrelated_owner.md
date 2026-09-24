# A call frees a lent allocation beside an unrelated owner

`box_release` lends `boxed(box)`, which packages the allocation authority for
`box->data` together with the whole allocated cell, to `box_destroy`, which
frees it. The caller also owns `object(other)`. This is the shape of
`examples/arena`'s `arena_pipeline`, whose every path ends in
`arena_destroy(arena)` while the caller still owns its region descriptors.

The call rule must know that nothing the caller keeps refers to the freed
allocation, and here it knows it from ownership alone. It reads what the
caller lent at the call's entry, so the retired allocation is named through
the value `box->data` had when the caller handed it over rather than a
post-call load the callee could have rewritten. One owned memory fact the
caller lent, `box->data[0..1]`, covers every byte of that allocation, and
owned memory is exclusive within one valid composition, so the owned
`object(other)` the caller kept is disjoint from it by construction. No
written `separate(..)` fact is needed.

Both halves are needed. Reading the lent resources after the call would let a
callee that frees `box->data` and re-points it at the caller's kept memory
make the lent owners appear to cover that memory
(`call_retires_the_allocation_it_was_lent_not_the_one_it_returns.md`). The
partition speaks only for kept *owned* memory, and only when a lent owner
covers the whole allocation: a kept range inside the allocation and a kept
view that may alias it are still refused
(`call_refuses_a_kept_range_inside_the_allocation_it_retires.md`,
`call_refuses_a_kept_view_that_may_alias_the_allocation_it_frees.md`).

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
    execute();
    simp();
}
```

```expect
pass
```
