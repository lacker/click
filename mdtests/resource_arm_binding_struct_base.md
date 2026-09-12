# Struct-pointer arm bindings as memory bases

A context frame keyed by the focused child owns its parent's cells through the
`parent` binding of the matched constructor. The binding is declared
`struct tree_node*` by `Context::Left`, so inside the arm it is a struct base:
`owns parent->left;` covers exactly that cell, `tree_at(parent->right)` names
the sibling subtree, and `fact parent->left == child` links the frame to the
node it is keyed by.

```c filename=resource_arm_binding_struct_base.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

void frame_top(struct tree_node *child) {}

void frame_push(
    struct tree_node *parent,
    struct tree_node *child,
    struct tree_node *sibling,
    int value
) {
    parent->value = value;
    parent->left = child;
    parent->right = sibling;
}

int frame_parent_value(struct tree_node *child, struct tree_node *parent) {
    return parent->value;
}

struct tree_node *frame_focus(struct tree_node *child, struct tree_node *parent) {
    return parent->left;
}
```

```click
verifying "resource_arm_binding_struct_base.c";

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

resource ctx_at(child: struct tree_node*) {
    field model: Context;
    match model {
        Context::Top => {},
        Context::Left(parent, value, sibling_model, up_model) => {
            owns parent->value;
            owns parent->left;
            owns parent->right;
            owns sibling: tree_at(parent->right);
            owns up: ctx_at(parent);
            fact parent != 0;
            fact parent->left == child;
            fact parent->value == value;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
    }
}

void frame_top(struct tree_node* child) {
    produces ctx: ctx_at(child);
    ensures ctx.model == Context::Top;
} by {
    execute();
    let ctx = fold(ctx_at(child), { model: Context::Top }, {});
    simp();
}

void frame_push(struct tree_node* parent, struct tree_node* child,
                struct tree_node* sibling, int value) {
    consumes parent->value;
    consumes parent->left;
    consumes parent->right;
    consumes s: tree_at(sibling);
    consumes u: ctx_at(parent);
    requires parent != 0;
    produces ctx: ctx_at(child);
    ensures ctx.model == Context::Left(parent, value, old(s.model), old(u.model));
} by {
    execute();
    let ctx = fold(ctx_at(child), {
        model: Context::Left(parent, value, s.model, u.model)
    }, { sibling: s, up: u });
    simp();
}

int frame_parent_value(struct tree_node* child, struct tree_node* parent) {
    owns ctx: ctx_at(child);
    requires ctx.model == Context::Left(parent, 7, HeapTree::Empty, Context::Top);
    ensures result == 7;
    ensures ctx.model == old(ctx.model);
} by {
    unfold(ctx) as { sibling: s, up: u };
    have s.model == HeapTree::Empty by { simp(); }
    unfold(s);
    execute();
    let s = fold(tree_at(parent->right), { model: HeapTree::Empty });
    let ctx = fold(ctx_at(child), { model: old(ctx.model) }, { sibling: s, up: u });
    simp();
}

struct tree_node* frame_focus(struct tree_node* child, struct tree_node* parent) {
    owns ctx: ctx_at(child);
    requires ctx.model == Context::Left(parent, 7, HeapTree::Empty, Context::Top);
    ensures result == child;
    ensures ctx.model == old(ctx.model);
} by {
    unfold(ctx) as { sibling: s, up: u };
    execute();
    let ctx = fold(ctx_at(child), { model: old(ctx.model) }, { sibling: s, up: u });
    simp();
}
```

```expect
pass
```
