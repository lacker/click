# A loop binder's model at the head is only what the invariants say

The loop head is an arbitrary visit, so the binder's model there is arbitrary
too. This loop declares `owns c: counter(p);` and states nothing about
`c.count`, so the model at loop exit is unknown and the postcondition claiming
it is unchanged is refused — even though this body never touches the cell.

```c filename=loop_binder_model_needs_an_invariant.c
struct cell { int32 value; };

void spin(struct cell* p, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}
```

```click
verifying "loop_binder_model_needs_an_invariant.c";

resource counter(p: struct cell*) {
    field count: int32;
    owns p->value;
    fact p->value == count;
}

void spin(struct cell* p, int32 n) {
    requires n >= 0;
    owns c: counter(p);
    ensures c.count == old(c.count);
} by {
    step();
    step();
    loop {
        owns c: counter(p);
        invariant i >= 0;
        invariant i <= n;

        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
fail: ensures c.count == old(c.count)
```
