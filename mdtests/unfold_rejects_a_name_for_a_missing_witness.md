# `let { slot: name } = unfold(r)` names only the body's witnesses

`holder_of`'s body declares the witness `cell`, not `target`.

```c filename=unfold_rejects_a_name_for_a_missing_witness.c
struct holder {
    int32 count;
    int32* target;
};

void bump(struct holder* h) {
    h->count = h->count + 1;
}
```

```click
resource holder_of(h: struct holder*) {
    owns *h;
    let cell: int32* where h->target == cell and (h->count < 200 or cell == 0);
}

verifying "unfold_rejects_a_name_for_a_missing_witness.c";

void bump(struct holder* h) {
    requires h != 0;
    requires h->count < 100;
    owns holder_of(h);
} by {
    let { target: p } = unfold(holder_of(h));
    step_until(function.exit);
    fold(holder_of(h));
    close();
}
```

```expect
fail: `target` is not a witness of this resource's body; its witnesses are `cell`
```
