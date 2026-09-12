# The colliding arm binding is renamed, so the true unfold closes

The positive companion of
[`spec_function_arm_binding_capture.md`](spec_function_arm_binding_capture.md).
The pure definition and the C function are the same, colliding names and all:
`reparent`'s `Node` arm binds `parent`, and the caller passes its own `parent`.
Substitution renames the arm binding before the argument reaches the arm body,
so `unfold` instantiates the definition as written and the *true* equation —
the second payload of the result is the argument — is what closes. Nothing in
the sidecar spells the rename; it is internal to substitution, and the arm's
own name is still `parent` in the source.

```c filename=rename.c
struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
};

int probe(struct rb_node *node, struct rb_node *parent) {
    return 0;
}
```

```click
verifying "rename.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, struct rb_node*, Color, RbTree, RbTree),
}

function reparent(tree: RbTree, fresh: struct rb_node*) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, parent, color, left, right) =>
            RbTree::Node(identity, fresh, color, left, right),
    }
}

int probe(struct rb_node* node, struct rb_node* parent) {
    requires node != parent;
    ensures result == 0;
} by {
    have reparent(
            RbTree::Node(node, node, Color::Red, RbTree::Empty, RbTree::Empty), parent)
        == RbTree::Node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty) by {
        unfold(reparent(
            RbTree::Node(node, node, Color::Red, RbTree::Empty, RbTree::Empty), parent));
        normalize();
    }
    execute();
    simp();
}
```

```expect
pass
```
