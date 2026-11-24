# Exits that own different things do not join

`give` leaves its `while (true)` by a `break` on both paths. One path hands
`q[0..1]` to `take`, which consumes it; the other keeps it. The loop declares
no binder that could describe the difference, and ownership is not something
the join abstracts: the successor would own `q[0..1]` on one path and not on
the other.

The join compares the exits' resources after the merges the resource algebra
defines, which fold together two descriptions of one authority and never make
an owned range out of none. The exits stay different and the loop is refused,
naming resource ownership.

```c filename=give.c
void take(int32* q);

void give(int32* p, int32* q, int32 flag) {
    while (true) {
        if (flag == 0) {
            take(q);
            break;
        } else {
            break;
        }
    }
}
```

```click
verifying "give.c";

extern void take(int32* q) {
    consumes q[0..1];
}

void give(int32* p, int32* q, int32 flag) {
    owns p[0..1];
    consumes q[0..1];
} by {
    loop {
        decreases 0;
        owns p[0..1];
        owns q[0..1];

        maintain by {
            if flag == 0 {
                step();
                step();
                step();
            } else {
                step();
                step();
            }
        }
    }
    step();
    close();
}
```

```expect
fail: so they have no common successor: resource ownership
```
