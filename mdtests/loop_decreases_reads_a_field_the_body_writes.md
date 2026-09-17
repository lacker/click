# a measure may read a cell the loop writes

The loop has no local at all: each iteration lowers `box->len` by one until it
reaches zero, and the measure is the field itself. It decreases only because
the back-edge ranking obligation reads the field in the back-edge memory,
after the store, and compares it with the read in the memory the iteration
started from. A value read once before the loop would never be seen to move.

```c filename=loop_decreases_reads_a_field_the_body_writes.c
struct box {
    int32 len;
};

int32 drain(struct box* box) {
    while (box->len > 0) {
        box->len = box->len - 1;
    }
    return box->len;
}
```

```click
verifying "loop_decreases_reads_a_field_the_body_writes.c";

int32 drain(struct box* box) {
    owns box->len;
    requires box->len >= 0;
    ensures result == 0;
} by {
    loop {
        decreases box->len;
        invariant 0 <= box->len;
        initialize by simp;
        preserve by {
            have 0 <= box->len - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(box->len)) using {
                    box->len > 0;
                }
            }
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
