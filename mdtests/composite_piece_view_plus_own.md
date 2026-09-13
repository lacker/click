# A function may view a composite and own one field inside it

The function views the unchanged `n->next` field and owns the `n->value`
field it updates. The two ranges are disjoint, so the stable view does not
conflict with the write. The store verifies with no effect clause: the write
footprint is exactly the owned field.

```c filename=composite_piece_view_plus_own.c
struct node {
    int32 value;
    struct node* next;
};

void set_value(struct node* n, int32 v) {
    n->value = v;
}
```

```click
resource cell(n: struct node*) {
    owns n->value;
    owns n->next;
}

verifying "composite_piece_view_plus_own.c";

void set_value(struct node* n, int32 v) {
    views n->next;
    owns n->value;
    ensures n->value == v;
} by {
    step();
    step();
    simp();
}
```

```expect
pass
```
