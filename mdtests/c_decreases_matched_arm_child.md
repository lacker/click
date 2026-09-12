# a matched arm's named child is a structural measure child

`decreases t;` names a contract resource binder, so the measure is the
instance `t` holds at entry. `tree_at` carries a model, so its children live
in the `HeapTree::Node` arm rather than in an `if`-guarded body; that arm's
`owns left:` and `owns right:` children are the direct contained children the
recursive call must pass. The arm is selected by a fact of its own that the
other arm denies: `fact p != 0` against `HeapTree::Empty`'s `fact p == 0`.

```c filename=c_decreases_matched_arm_child.c
struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 tree_depth_ok(struct node* root) {
    if (root == 0) {
        return 1;
    }
    if (tree_depth_ok(root->left) == 0) {
        return 0;
    }
    return tree_depth_ok(root->right);
}
```

```click
verifying "c_decreases_matched_arm_child.c";

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

int32 tree_depth_ok(struct node* root) {
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
            unfold(t) as { left: l, right: r };
            branch {
                then { step(); simp(); }
                else {}
            }
            step(tree_depth_ok(root->left), { t: l });
            branch {
                then {
                    step();
                    let t = fold(tree_at(root), { model: old(t.model) }, { left: l, right: r });
                    simp();
                }
                else {}
            }
            step(tree_depth_ok(root->right), { t: r });
            step();
            let t = fold(tree_at(root), { model: old(t.model) }, { left: l, right: r });
            simp();
        },
    }
}
```

```expect
pass
```
