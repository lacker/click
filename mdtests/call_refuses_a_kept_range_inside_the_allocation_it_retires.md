# A call refuses to retire an allocation beside a kept range inside it

`box_take` consumes `half_boxed(box)`, which holds the allocation authority
for an 8-byte `box->data` but owns only its first element, and returns an
allocation whose relation to `box->data` its contract does not state. For the
caller the input allocation is therefore retired by the call. The caller
keeps `box->data[1..2]`, a range inside that allocation, so the call must be
refused: nothing the caller holds says the kept range is outside what the
callee may have released, and the lent resources do not own the whole
allocation.

```c filename=box.c
struct box {
    int32* data;
};

int32* box_take(struct box* box) {
    return box->data;
}

void box_release(struct box* box) {
    box_take(box);
}
```

```click
resource half_boxed(box: struct box*) {
    owns object(box);
    contains allocation(box->data, 8);
    owns box->data[0..1];
}

verifying "box.c";

int32* box_take(struct box* box) {
    consumes half_boxed(box);
    produces object(box);
    produces allocation(result, 8);
    produces result[0..1];
} by {
    unfold(half_boxed(box));
    execute();
    simp();
}

void box_release(struct box* box) {
    consumes half_boxed(box);
    produces object(box);
    owns box->data[1..2];
} by {
    execute();
    simp();
}
```

```expect
fail: resource would remain usable after its allocation is freed
```
