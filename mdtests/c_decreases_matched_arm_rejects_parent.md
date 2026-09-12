# a matched measure refuses a call that stays on the same node

The measure is the instance `t` holds at entry, and the `HeapTree::Node` arm's
children are `tree_at(p->left)` and `tree_at(p->right)`. A recursive call that
passes `root` again is not one of them, so the structural measure is refused
even though the ordinary contract would transfer the same instance back.

```c filename=c_decreases_matched_arm_rejects_parent.c
struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 tree_spin(struct node* root) {
    if (root == 0) {
        return 1;
    }
    return tree_spin(root);
}
```

```click
verifying "c_decreases_matched_arm_rejects_parent.c";

spec enum HeapTree {
    Empty,
    Node(struct node*, int32, HeapTree, HeapTree),
}

resource tree_at(p: struct node*) {
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

int32 tree_spin(struct node* root) {
    owns t: tree_at(root);
    decreases t;
    ensures t.model == old(t.model);
} by {
    match t.model {
        HeapTree::Empty => {
            unfold(t);
            execute();
            let t = fold(tree_at(root), { model: HeapTree::Empty });
            simp();
        },
        HeapTree::Node(identity, value, left_model, right_model) => {
            branch {
                then { step(); simp(); }
                else {}
            }
            step(tree_spin(root), { t: t });
            step();
            simp();
        },
    }
}
```

```expect
fail: does not pass a direct contained child
```
