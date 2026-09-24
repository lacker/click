# Consecutive reallocating calls keep the returned allocation readable

`box_renew` replaces `box->data` with a fresh allocation holding the same
value and frees the old one; its contract consumes and produces `boxed(box)`
without saying whether the pointer changed. A caller that renews twice and
then reads `box->data[0]` must still find the cell through the `boxed(box)`
the second call produced, and must still relate the value to the one it
started with.

This pins a pattern that a change to the call rule's allocation retirement
must keep: reading the lent resources at the call's entry, so that each call
retires the allocation it was actually handed, made the second read fail
with a missing `views` fact, because the retirement and returned-claim edges
it then records hide the pointer field from the block walk
(`ContractAllocationClaimsChanged` is not shown separate for a block).

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
