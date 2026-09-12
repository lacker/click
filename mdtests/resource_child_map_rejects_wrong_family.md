# a fold child map must supply each slot's own family

The `right` slot owns a `tree_at`; supplying the frame instance for it is
rejected before the proof runs.

```c filename=resource_child_map_rejects_wrong_family.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

void frame_push(
    struct tree_node *node,
    struct tree_node *up,
    struct tree_node *sibling
) {
    node->right = sibling;
}
```

```click
verifying "resource_child_map_rejects_wrong_family.c";

spec enum HeapTree {
    Empty,
    Node(struct tree_node*, int, HeapTree, HeapTree),
}

spec enum Context {
    Top,
    Left(HeapTree, Context),
}

resource tree_at(p: struct tree_node*) {
    field model: HeapTree;
    match model {
        HeapTree::Empty => { fact p == 0; },
        HeapTree::Node(identity, value, left_model, right_model) => {
            owns p->value;
            owns p->left;
            owns p->right;
            owns left: tree_at(p->left);
            owns right: tree_at(p->right);
            fact p != 0;
            fact p == identity;
            fact p->value == value;
            fact left.model == left_model;
            fact right.model == right_model;
        },
    }
}

resource ctx_at(node: struct tree_node*) {
    field model: Context;
    match model {
        Context::Top => {},
        Context::Left(right_model, up_model) => {
            owns node->right;
            owns right: tree_at(node->right);
            owns up: ctx_at(node->right);
            fact node != 0;
            fact right.model == right_model;
            fact up.model == up_model;
        },
    }
}

void frame_push(struct tree_node* node, struct tree_node* up,
                struct tree_node* sibling) {
    consumes node->right;
    consumes s: tree_at(sibling);
    consumes u: ctx_at(up);
    requires node != 0;
    produces ctx: ctx_at(node);
    ensures ctx.model == Context::Left(old(s.model), old(u.model));
} by {
    execute();
    let ctx = fold(ctx_at(node), {
        model: Context::Left(s.model, u.model)
    }, { right: u, up: s });
    simp();
}
```

```expect
fail: child `u` is `ctx_at`, but slot `right` of `ctx_at` owns `tree_at`
```
