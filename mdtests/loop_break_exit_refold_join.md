# A `break` after a refold joins through the loop binder

`maybe_swap` relinks the root's two children and refolds `tree_at(root)` with
the mirrored model before leaving; the other `break` refolds the model it
started with. That is the shape of a rotation step inside a fixup loop: the
binder's model and two of the cells it owns differ between the loop's exits.

A23 refused the loop here, because its exits reached different states. They are
now joined through the binder: `t` is rebound at each exit by family and
argument equality, its model becomes one fresh name, the two link cells become
fresh values, and each exit contributes the equations pinning them as its own
disjunct. What *every* exit states — that the root is a real node — survives
the join as an ordinary fact, which is what this postcondition reads.

A claim that has to distinguish the exits reads the exported disjunction with
`cases`; see
[`loop_break_exit_binder_model_join.md`](loop_break_exit_binder_model_join.md).

```c filename=maybe_swap.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

struct tree_node *maybe_swap(struct tree_node *root, int flag) {
    struct tree_node *l;
    struct tree_node *r;

    while (true) {
        l = root->left;
        r = root->right;
        if (flag == 0) {
            root->left = l;
            root->right = r;
            break;
        } else {
            root->left = r;
            root->right = l;
            break;
        }
    }
    return root;
}
```

```click
verifying "maybe_swap.c";

spec enum HeapTree {
    Empty,
    Node(struct tree_node*, int, HeapTree, HeapTree),
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

struct tree_node* maybe_swap(struct tree_node* root, int flag) {
    owns t: tree_at(root);
    requires t.model != HeapTree::Empty;
    ensures result != 0;
} by {
    step();
    step();
    loop {
        owns t: tree_at(root);
        invariant t.model != HeapTree::Empty;

        initialize by simp;
        preserve by {
            match t.model {
                HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
                HeapTree::Node(node, value, left_model, right_model) => {
                    unfold(t) as { left: lt, right: rt };
                    step();
                    step();
                    if flag == 0 {
                        step();
                        step();
                        step();
                        let t = fold(tree_at(root), {
                            model: HeapTree::Node(node, value, left_model, right_model)
                        }, { left: lt, right: rt });
                        step();
                    } else {
                        step();
                        step();
                        step();
                        let t = fold(tree_at(root), {
                            model: HeapTree::Node(node, value, right_model, left_model)
                        }, { left: rt, right: lt });
                        step();
                    }
                },
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
