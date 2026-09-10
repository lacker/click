# A loop may own a composite the function owns

The loop declares `owns cell(node)`, so its body unfolds that composite and
writes the field it owns. The function's other owned memory, `q[0..1]`, is
outside the loop's footprint and keeps its pre-loop value with no invariant
naming `q`.

```c filename=loop_owns_composite_resource.c
struct cell {
    int32 value;
};

void loop_owns_composite_resource(struct cell* node, int32 q[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        node->value = i;
        i = i + 1;
    }
}
```

```click
resource cell(node: struct cell*) {
    owns node->value;
}

verifying "loop_owns_composite_resource.c";

void loop_owns_composite_resource(struct cell* node, int32 q[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(q[0..1]);
    owns cell(node);
    owns q[0..1];
    requires separate(memory(node[0..1]), memory(q[0..1]));
    ensures q_preserved: q[0] == old(q[0]);
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
