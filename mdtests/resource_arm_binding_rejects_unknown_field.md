# An arm binding's struct must declare the named field

A struct-pointer arm binding resolves its fields against the declared layout of
its struct, so a field that `struct tree_node` does not have is refused by name
rather than lowered to a load of unknown width.

```c filename=resource_arm_binding_rejects_unknown_field.c
struct tree_node {
    int value;
    struct tree_node *left;
};

int read_value(struct tree_node *node) { return node->value; }
```

```click
verifying "resource_arm_binding_rejects_unknown_field.c";

spec enum Frame {
    Empty,
    One(struct tree_node*, int32),
}

resource frame_at(p: struct tree_node*) {
    field model: Frame;
    match model {
        Frame::Empty => { fact p == 0; },
        Frame::One(parent, count) => {
            owns parent->weight;
            fact p == parent;
        },
    }
}

int read_value(struct tree_node* node) {
    owns f: frame_at(node);
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: struct `tree_node` has no field `weight`
```
