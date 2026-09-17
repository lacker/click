# a loop measure may read memory

The loop counts a local toward a bound that lives in a struct field. The C
keeps no local copy of the bound, so the only decreasing quantity is the
distance from `i` to `box->len`, and the measure has to read the field to name
it. The loop does not write the field; the measure's value at the back edge is
its evaluation in the back-edge state, like any invariant's.

```c filename=loop_decreases_reads_a_field.c
struct box {
    int32 len;
};

int32 count_to_len(struct box* box) {
    int32 i;
    i = 0;
    while (i < box->len) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_decreases_reads_a_field.c";

int32 count_to_len(struct box* box) {
    views box->len;
    requires box->len >= 0;
    ensures result == box->len;
} by {
    step();
    step();
    loop {
        decreases box->len - i;
        invariant 0 <= i and i <= box->len;
    }
    step();
    simp();
}
```

```expect
pass
```
