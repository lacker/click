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
value, it asks for a proved separation between each resource the caller keeps
and the retired allocation, and refuses the call when it finds none.

A written `separate(memory(other[0..2]), memory(box->data[0..1]))` cannot
supply it either, and the reason is the root of this gap: the call rule
expands the lent resources under the memory *after* the call, so the retired
allocation is named through the post-call value of `box->data`, a fresh load
the callee could have rewritten, not the pointer the caller handed over. A
fact about the entry value never mentions it.

The intended rule has two parts. The lent resources are read at the call's
entry, so the call retires the allocation it was actually given; and a kept
owned memory fact is then separate from that allocation whenever one owned
memory fact the caller lent covers the allocation's whole byte range, because
the two were held at once and owned memory is exclusive. With the first part
alone, the second is unsound: a callee that frees `box->data` and re-points
it at the caller's kept memory would make the post-call lent resources
"cover" that memory.

Reading at entry is not yet landable: it makes each consume/produce of an
allocation-bearing composite whose pointer field the callee owns retire the
old claim and install a new one, and a second such call then hides the field
from the block walk
(`consecutive_reallocating_calls_keep_the_returned_allocation_readable.md`
pins the pattern that must keep working). Until that is fixed, this fixture
should keep failing as below; once it passes, rename it and prove it with
`execute(); simp();`.

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
