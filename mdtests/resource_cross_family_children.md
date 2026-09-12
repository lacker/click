# Cross-family children in matched arms

A context frame owns its node's cells, the sibling subtree as a `tree_at`
instance, and the frame above it as a `ctx_at` instance. The two families are
declared independently: `ctx_at` owns a `tree_at`, and `tree_at` never owns a
`ctx_at`. The empty `Top` frame owns nothing at all.

```c filename=resource_cross_family_children.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

void frame_top(struct tree_node *node) {}

void frame_push(
    struct tree_node *node,
    struct tree_node *up,
    struct tree_node *sibling,
    int value
) {
    node->value = value;
    node->right = sibling;
}

int frame_value(struct tree_node *node, struct tree_node *up) {
    return node->value;
}
```

```click
verifying "resource_cross_family_children.c";

spec enum HeapTree {
    Empty,
    Node(struct tree_node*, int, HeapTree, HeapTree),
}

spec enum Context {
    Top,
    Left(struct tree_node*, int, HeapTree, Context),
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
        Context::Left(up_node, value, right_model, up_model) => {
            owns node->value;
            owns node->left;
            owns node->right;
            owns right: tree_at(node->right);
            owns up: ctx_at(up_node);
            fact node != 0;
            fact node->value == value;
            fact right.model == right_model;
            fact up.model == up_model;
        },
    }
}

void frame_top(struct tree_node* node) {
    produces ctx: ctx_at(node);
    ensures ctx.model == Context::Top;
} by {
    execute();
    let ctx = fold(ctx_at(node), { model: Context::Top }, {});
    simp();
}

void frame_push(struct tree_node* node, struct tree_node* up,
                struct tree_node* sibling, int value) {
    consumes node->value;
    consumes node->left;
    consumes node->right;
    consumes s: tree_at(sibling);
    consumes u: ctx_at(up);
    requires node != 0;
    produces ctx: ctx_at(node);
    ensures ctx.model == Context::Left(up, value, old(s.model), old(u.model));
} by {
    execute();
    let ctx = fold(ctx_at(node), {
        model: Context::Left(up, value, s.model, u.model)
    }, { right: s, up: u });
    simp();
}

int frame_value(struct tree_node* node, struct tree_node* up) {
    owns ctx: ctx_at(node);
    requires ctx.model == Context::Left(up, 7, HeapTree::Empty, Context::Top);
    ensures result == 7;
    ensures ctx.model == old(ctx.model);
} by {
    unfold(ctx) as { right: r, up: u };
    have r.model == HeapTree::Empty by { simp(); }
    unfold(r);
    execute();
    let r = fold(tree_at(node->right), { model: HeapTree::Empty });
    let ctx = fold(ctx_at(node), { model: old(ctx.model) }, { right: r, up: u });
    simp();
}
```

```expect
pass
```
