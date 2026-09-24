# A call retires the allocation it was lent, not the one it leaves behind

`box_repoint` frees `box->data` and re-points the field at `other`, memory
its caller owns and keeps across the call along with `other`'s allocation
authority. The call rule must retire the allocation the caller lent, named
by the entry value of `box->data`, and must not reach `other`, which the
caller then writes and frees.

This is the program that makes reading the lent resources *after* the call
unsound in combination with the ownership partition
(`call_retires_allocation_beside_unrelated_owner.md`): expanded at the
post-call state, the lent `boxed(box)` would name `box->data == other`, its
owned `box->data[0..1]` would appear to cover `other`'s allocation, and the
kept `other[0..1]` would pass as disjoint from the allocation being retired.
A fixture cannot show that misreading refused, because the kernel has no
post-call reading left to select, so this one pins the positive half: the
rule retires the entry allocation, the caller keeps its authority over
`other`, and the write and free that follow verify.

```c filename=box.c
struct box {
    int32* data;
};

void box_repoint(struct box* box, int32* other) {
    free(box->data);
    box->data = other;
}

void box_release(struct box* box, int32* other) {
    box_repoint(box, other);
    *other = 1;
    free(other);
}
```

```click
resource boxed(box: struct box*) {
    owns object(box);
    contains allocation(box->data, 4);
    owns box->data[0..1];
}

verifying "box.c";

void box_repoint(struct box* box, int32* other) {
    consumes boxed(box);
    produces object(box);
    ensures box->data == other;
} by {
    unfold(boxed(box));
    execute();
    simp();
}

void box_release(struct box* box, int32* other) {
    consumes boxed(box);
    produces object(box);
    consumes allocation(other, 4);
    consumes other[0..1];
} by {
    execute();
    simp();
}
```

```expect
pass
```
