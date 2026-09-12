# A loop body cannot write through an instance the loop withheld

The function holds two counters. The loop declares only `owns c: counter(p);`,
so `d` stays with the enclosing frame and the cell it owns is neither the
loop's to read nor the loop's to write. The body's access to `q->value` fails
for want of that authority: all the body holds is the instance the header
named.

```c filename=loop_binder_rejects_undeclared_instance_write.c
struct cell { int32 value; };

void bump_other(struct cell* p, struct cell* q, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        q->value = q->value + 1;
        i = i + 1;
    }
}
```

```click
verifying "loop_binder_rejects_undeclared_instance_write.c";

resource counter(p: struct cell*) {
    field count: int32;
    owns p->value;
    fact p->value == count;
}

void bump_other(struct cell* p, struct cell* q, int32 n) {
    requires n >= 0;
    requires n <= 1000;
    owns c: counter(p);
    owns d: counter(q);
    requires d.count == 0;
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
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
fail: missing resource fact
```
