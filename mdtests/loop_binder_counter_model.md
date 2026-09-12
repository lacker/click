# A loop binder carries a model the body updates

`bump_n` increments one counted cell `n` times. The loop binds the counter
with `owns c: counter(p);`, and the invariant states the model exactly:
`c.count == old(c.count) + i`. Each iteration unfolds the instance, writes the
cell it owns, and folds it again with the new model, so the back edge finds a
`counter(p)` at the same argument with the model the invariant demands. After
the loop, `c` is the final instance and the negated guard turns the invariant
into the postcondition.

```c filename=loop_binder_counter_model.c
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
verifying "loop_binder_counter_model.c";

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
    ensures c.count == old(c.count) + n;
} by {
    step();
    step();
    loop {
        owns c: counter(p);
        invariant i >= 0;
        invariant i <= n;
        invariant c.count == old(c.count) + i;

        initialize by simp;
        preserve by {
            unfold(c);
            step();
            step();
            let c = fold(counter(p), { count: old(c.count) + i });
            close_invariants();
        }
    }
    have i == n by simp;
    execute();
    simp();
}
```

```expect
pass
```
