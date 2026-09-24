# A call refuses to free a lent allocation beside a kept view that may alias it

`box_destroy` frees `box->data`, which the caller lends inside `boxed(box)`.
The caller also keeps `views q[0..1]` for an unrelated parameter `q`. A view
is not an owner, so ownership exclusivity says nothing about it, and no fact
separates `q` from the freed allocation: `q` may point into it. The call is
refused with the stale-resource reason.

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

void box_release(struct box* box, struct box* other, int32* q) {
    consumes boxed(box);
    produces object(box);
    owns object(other);
    views q[0..1];
} by {
    execute();
    simp();
}
```

```expect
fail: resource would remain usable after its allocation is freed
```
