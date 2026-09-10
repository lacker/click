# A function may view a composite and own one field inside it

`views cell(n)` gives read authority over the whole node, and `owns n->value`
gives write authority over one field of it. The two compose because the owned
piece lies inside the viewed composite; a view never conflicts with ownership
of a part it covers. The store into the owned field verifies with no effect
clause: the write footprint is exactly the owned field.

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
    views cell(n);
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
