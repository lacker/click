# an opaque reallocating call does not carry an unstated value

`box_renew` is external and its contract hands back `boxed(box)` with nothing
said about the cell `box->data[0]`, which may now live in a different
allocation. The claim that the value read after the call equals the entry
value is refused. Both sides spell the same path, so the diagnostic asks the
resource tracker about one address at two program points; here the two reads
are of different load pointers, and the diagnostic must still be produced
rather than lost. It is the one-call, unverified-callee negative of
[`consecutive_reallocating_calls_keep_the_returned_allocation_readable`](consecutive_reallocating_calls_keep_the_returned_allocation_readable.md).

```c filename=opaque_reallocating_call_does_not_carry_an_unstated_value.c
struct box {
    int32* data;
};

extern void box_renew(struct box* box);

int32 box_cycle(struct box* box) {
    box_renew(box);
    return box->data[0];
}
```

```click
resource boxed(box: struct box*) {
    owns *box;
    owns box->data[0..1];
    fact separate(memory(*box), memory(box->data[0..1]));
}

verifying "opaque_reallocating_call_does_not_carry_an_unstated_value.c";

extern void box_renew(struct box* box) {
    owns boxed(box);
}

int32 box_cycle(struct box* box) {
    owns boxed(box);
    ensures result == old(box->data[0]);
} by {
    step();
    step();
    close();
}
```

```expect
fail: unclosed goal
```
