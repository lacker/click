# A terminal proof case split is certified once per case

`free(box)` is valid only in the case `box != 0`, where unfolding
`owned_box(box)` grants the allocation. The proof splits on `box != 0` at
entry and both arms run to the return. The checked join keeps each case's
outcome path with its own resources, and kernel certification runs once per
recorded case with that case's fact assumed at entry, so the free is
certified under `box != 0`. A single caseless certification would reject
the free as invalid.

```c filename=box_destroy.c
struct box {
    int32 value;
};

int32 box_destroy(struct box *box) {
    free(box);
    return 0;
}
```

```click
resource owned_box(box: struct box*) {
    if box != 0 {
        contains allocation(box, sizeof(struct box));
        owns object(box);
    }
}

verifying "box_destroy.c";

int32 box_destroy(struct box* box) {
    consumes owned_box(box);
    ensures result == 0;
} by {
    if box != 0 {
        unfold(owned_box(box));
        execute();
        simp();
    } else {
        unfold(owned_box(box));
        execute();
        simp();
    }
}
```

```expect
pass
```
