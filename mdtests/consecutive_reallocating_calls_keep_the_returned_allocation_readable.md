# Consecutive reallocating calls keep the returned allocation readable

`box_renew` replaces `box->data` with a fresh allocation holding the same
value and frees the old one; its contract consumes and produces `boxed(box)`
without saying whether the pointer changed. A caller that renews twice and
then reads `box->data[0]` must still find the cell through the `boxed(box)`
the second call produced, and must still relate the value to the one it
started with.

The call rule reads the lent `boxed(box)` at each call's entry, so each call
retires the allocation it was handed and installs the one it returns, right
after its own havoc. The returned composite's fields are named at that havoc,
and a later read of `box->data` must be named there too. It is: the
retirement is covered by the havoc's range `box->data[0..1]`, so the naming
walk crosses it (`RetirementInsideItsCallHavoc`, see
`docs/internals/resource-tracker.md`). Before that rule, the read after the
first call was named at the retirement and related to the field only through
a heap-extent proof, and the second call nested a second such proof inside
the first, so the read failed with a missing `views` fact.
`three_consecutive_reallocating_calls_keep_the_returned_allocation_readable.md`
and the four-call form extend the chain, and
`consecutive_reallocating_calls_do_not_carry_an_unstated_value.md` is the
negative.

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
