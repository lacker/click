# a path fact that refutes an arm decides the instance's model

Arm selection reads the premises forward: `c.model != Maybe::None` leaves one
arm. The same decision runs backwards. A folded instance's body holds wherever
the instance is held, so a premise that contradicts an arm's own fact says the
model is not that constructor.

`tree_at`'s `HeapTree::Empty` arm states `fact p == 0` and its `HeapTree::Node`
arm states `fact p != 0`, so the guard on the child link decides the child's
model both ways. `root->left != 0` publishes `left.model != HeapTree::Empty`,
the `Excluded` evidence arm selection reads. `root->left == 0` refutes the
`Node` arm instead, and because the surviving `Empty` arm carries no fields it
has only one value, so the equation itself is published.

Only a fact that names no binding of its own arm takes part: a binding is an
unknown the constructor would supply, so a fact about one says nothing until
the arm is selected.

```c filename=resource_refuted_arm_model_fact.c
struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 probe_present(struct node *root) {
    return 0;
}

int32 probe_absent(struct node *root) {
    return 0;
}
```

```click
verifying "resource_refuted_arm_model_fact.c";

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

int32 probe_present(struct node* root) {
    owns t: tree_at(root);
    requires t.model != HeapTree::Empty;
    requires root->left != 0;
    ensures t.model == old(t.model);
} by {
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(identity, value, left_model, right_model) => {
            unfold(t) as { left: l, right: rt };
            have left_model != HeapTree::Empty by { assumption(); }
            execute();
            let t = fold(tree_at(root), {
                model: HeapTree::Node(identity, value, left_model, right_model)
            }, { left: l, right: rt });
            simp();
        },
    }
}

int32 probe_absent(struct node* root) {
    owns t: tree_at(root);
    requires t.model != HeapTree::Empty;
    requires root->left == 0;
    ensures t.model == old(t.model);
} by {
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(identity, value, left_model, right_model) => {
            unfold(t) as { left: l, right: rt };
            have left_model == HeapTree::Empty by { assumption(); }
            execute();
            let t = fold(tree_at(root), {
                model: HeapTree::Node(identity, value, left_model, right_model)
            }, { left: l, right: rt });
            simp();
        },
    }
}
```

```expect
pass
```
