# Consecutive reallocating calls do not carry an unstated value

The negative of
`consecutive_reallocating_calls_keep_the_returned_allocation_readable.md`:
`box_renew` now stores `0` in the fresh allocation, and its contract no
longer promises that `box->data[0]` survives. The naming walk crosses each
call's retirement of the old allocation, but only as far as that call's own
havoc, which covers every byte of it; it never reaches a value from before a
call. So the read after two calls is readable, and the claim that it equals
the entry value is refused.

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
    fresh[0] = 0;
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
fail: unclosed goal
```
