# Three consecutive reallocating calls keep the returned allocation readable

The three-call form of
`consecutive_reallocating_calls_keep_the_returned_allocation_readable.md`.
Each `box_renew` call retires the allocation it was lent and installs the
one it returns, and each retirement is covered by that call's own havoc, so
the naming walk carries `box->data` across every retirement to the call that
last wrote it. The read after the third call names the field exactly where the
third call's `produces boxed(box)` did, with no nested heap-extent proof per
earlier call.

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
