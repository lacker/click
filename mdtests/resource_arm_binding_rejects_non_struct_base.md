# A non-struct-pointer arm binding is not a memory base

Only a constructor field declared `struct tag*` gives a match-arm binding a
layout. `count` is declared `int32` by `Frame::One`, so `count->value` names no
cell and is refused where it is written, with the binding's declared type.

```c filename=resource_arm_binding_rejects_non_struct_base.c
struct tree_node {
    int value;
    struct tree_node *left;
};

int read_value(struct tree_node *node) { return node->value; }
```

```click
verifying "resource_arm_binding_rejects_non_struct_base.c";

spec enum Frame {
    Empty,
    One(int32, struct tree_node*),
}

resource frame_at(p: struct tree_node*) {
    field model: Frame;
    match model {
        Frame::Empty => { fact p == 0; },
        Frame::One(count, parent) => {
            owns count->value;
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
fail: match-arm binding `count` is declared `int32`, so `count->value` has no struct layout
```
