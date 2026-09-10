# A loop owning a composite may not write outside it

The loop declares `owns cell(node)`, so its authority is that composite alone.
The function's `q[0..1]` is viewed by the body, and the store `q[0] = i` is
rejected at the store.

```c filename=loop_owns_composite_rejects_outside_write.c
struct cell {
    int32 value;
};

void loop_owns_composite_rejects_outside_write(struct cell* node, int32 q[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        node->value = i;
        q[0] = i;
        i = i + 1;
    }
}
```

```click
resource cell(node: struct cell*) {
    owns node->value;
}

verifying "loop_owns_composite_rejects_outside_write.c";

void loop_owns_composite_rejects_outside_write(struct cell* node, int32 q[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(q[0..1]);
    owns cell(node);
    owns q[0..1];
    requires separate(memory(node[0..1]), memory(q[0..1]));
} by {
    step();
    step();
    loop {
        owns cell(node);
        invariant i >= 0;
        invariant i <= n;

        initialize by simp;
        preserve by {
            unfold(cell(node));
            step();
            step();
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
fail: missing resource fact
```
