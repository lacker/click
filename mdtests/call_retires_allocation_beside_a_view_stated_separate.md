# A call retires a lent allocation beside a view stated separate

`box_release` lends `boxed(box)` to `box_destroy`, which frees `box->data`,
and keeps a view of `q[0..1]`. The ownership partition does not speak for a
view, which may alias memory someone else owns, so the view needs a
separation the path facts prove. The contract states it:
`separate(memory(q[0..1]), memory(box->data[0..n]))` with `n == 1`. The
retired allocation is named through the entry value of `box->data`, the same
value the precondition names, so the stated fact reaches the retirement check
(whose allocation is four bytes from that base) once `n` is known.

Without the stated separation the same kept view is refused
(`call_refuses_a_kept_view_that_may_alias_the_allocation_it_frees.md`).

```c filename=box.c
struct box {
    int32* data;
};

void box_destroy(struct box* box) {
    free(box->data);
}

void box_release(struct box* box, struct box* other, int32* q, int32 n) {
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

void box_release(struct box* box, struct box* other, int32* q, int32 n) {
    consumes boxed(box);
    produces object(box);
    owns object(other);
    views q[0..1];
    requires n == 1;
    requires separate(memory(q[0..1]), memory(box->data[0..n]));
} by {
    execute();
    simp();
}
```

```expect
pass
```
