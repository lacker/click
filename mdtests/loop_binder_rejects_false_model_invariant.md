# A loop binder's model invariant is checked at the back edge

The body increments the counted cell and folds the counter with the model that
write produced. The invariant claims the model never changes, so the back edge
refuses the iteration.

```c filename=loop_binder_rejects_false_model_invariant.c
struct cell { int32 value; };

void bump_n(struct cell* p, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p->value = p->value + 1;
        i = i + 1;
    }
}
```

```click
verifying "loop_binder_rejects_false_model_invariant.c";

resource counter(p: struct cell*) {
    field count: int32;
    owns p->value;
    fact p->value == count;
}

void bump_n(struct cell* p, int32 n) {
    requires n >= 0;
    requires n <= 1000;
    owns c: counter(p);
    requires c.count == 0;
    ensures c.count == old(c.count);
} by {
    step();
    step();
    loop {
        owns c: counter(p);
        invariant i >= 0;
        invariant i <= n;
        invariant c.count == old(c.count);

        initialize by simp;
        preserve by {
            unfold(c);
            step();
            step();
            let c = fold(counter(p), { count: old(c.count) + i });
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
fail: closure body did not prove every invariant obligation
```
