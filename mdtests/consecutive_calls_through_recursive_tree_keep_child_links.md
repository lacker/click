# Consecutive calls through a recursive tree keep the caller's child links

The shape of `tree_contains` in `examples/modeled-binary-tree`. `both`
unfolds `tree_at(p)`, lends the left subtree to `touch`, then the right one,
and folds the node back. The fold compares each child's argument with
`p->left` and `p->right` read after both calls.

A recursive tree's footprint is every cell no other rule keeps. The caller
keeps owning the node's link cells outside each transfer, so each call's
havoc records them on its edge. The first call drops the cached `p->left`,
and nothing reads it before the second call, so the second edge used to
record nothing for it and the fold could not name `p->left` across both
calls. A call whose footprint reaches unnamed memory now records every flat
member of what the caller keeps owning.

```c filename=consecutive_calls_through_recursive_tree_keep_child_links.c
struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

void touch(struct node* p) {
}

void both(struct node* p) {
    if (p == 0) {
        return;
    }
    touch(p->left);
    touch(p->right);
}
```

```click
verifying "consecutive_calls_through_recursive_tree_keep_child_links.c";

spec enum Tree {
    Empty,
    Node(struct node*, int32, Tree, Tree),
}

resource tree_at(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(identity, value, left_model, right_model) => {
            owns p->value;
            owns &p->left;
            owns &p->right;
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

void touch(struct node* p) {
    owns t: tree_at(p);
    ensures t.model == old(t.model);
} by {
    execute();
    simp();
}

void both(struct node* p) {
    owns t: tree_at(p);
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => {
            unfold(t);
            execute();
            let t = fold(tree_at(p), { model: Tree::Empty });
            simp();
        },
        Tree::Node(identity, value, left_model, right_model) => {
            let { left: l, right: r } = unfold(t);
            branch {
                then { step(); simp(); }
                else {}
            }
            step(touch(p->left), { t: l });
            step(touch(p->right), { t: r });
            let t = fold(tree_at(p), { model: old(t.model) }, { left: l, right: r });
            execute();
            simp();
        },
    }
}
```

```expect
pass
```
