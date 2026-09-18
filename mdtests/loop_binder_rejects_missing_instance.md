# A loop body must hand its binder back at the back edge

The body unfolds the counter, writes the cell, and never folds it again. The
loop declared `owns c: counter(p);`, so the back edge looks for that instance
and refuses the iteration by name.

The head's model `c.count` is an arbitrary value of its own, so before touching
the cell the body states what the invariants make it: `c.count == i`. Nothing
else bounds the cell that the increment writes.

```c filename=loop_binder_rejects_missing_instance.c
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
verifying "loop_binder_rejects_missing_instance.c";

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
            have c.count == i by { simp() using { c.count == old(c.count) + i; old(c.count) == 0; } }
            unfold(c);
            step();
            step();
            close_invariants();
        }
    }
    have i == n by simp;
    execute();
    simp();
}
```

```expect
fail: loop binder `c` has no owned `counter` instance at its arguments here
```
