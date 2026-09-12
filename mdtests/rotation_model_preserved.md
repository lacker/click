# A left rotation preserves the modeled tree

The positive sibling of the three `rotation_model_rejects_*` tests. The C is
the ordinary left rotation: it moves the pivot's left subtree to the root's
right slot and hangs the root under the pivot. The contract consumes one
modeled tree and produces the returned tree with model
`heap_rotate_left(old(t.model))`, so the claim names every node address, every
payload, and all three subtrees.

The proof is the one the negatives reuse unchanged: match the entry model,
close the empty cases from the preconditions, unfold the root and the pivot,
run the four C statements, and fold the lower node and the returned pivot from
the exposed children. Each negative keeps this script and changes only the C,
so a failure there is about the model and not about proof syntax.

```c filename=rotation_model_preserved.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

struct tree_node *rotate_left(struct tree_node *root) {
    struct tree_node *pivot;
    struct tree_node *middle;

    pivot = root->right;
    middle = pivot->left;
    root->right = middle;
    pivot->left = root;
    return pivot;
}
```

```click
verifying "rotation_model_preserved.c";

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

function heap_right(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => right,
    }
}

function heap_rotate_left(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => match right {
            HeapTree::Empty => tree,
            HeapTree::Node(pivot_node, pivot_value, middle, far_right) =>
                HeapTree::Node(pivot_node, pivot_value,
                    HeapTree::Node(node, value, left, middle), far_right),
        },
    }
}

struct tree_node* rotate_left(struct tree_node* root) {
    consumes t: tree_at(root);
    requires t.model != HeapTree::Empty;
    requires heap_right(t.model) != HeapTree::Empty;
    produces rotated: tree_at(result);
    ensures rotated.model == heap_rotate_left(old(t.model));
} by {
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(node, value, left_model, right_model) => {
            have heap_right(t.model) == right_model by {
                rewrite(t.model == HeapTree::Node(node, value, left_model, right_model));
                unfold(heap_right(HeapTree::Node(node, value, left_model, right_model)));
                normalize();
            }
            have right_model != HeapTree::Empty by {
                rewrite(right_model == heap_right(t.model));
                assumption();
            }
            match right_model {
                HeapTree::Empty => { contradiction(right_model == HeapTree::Empty); },
                HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model) => {
                    unfold(t) as { left: l, right: r };
                    unfold(r) as { left: m, right: z };
                    execute();
                    let lower = fold(tree_at(root), {
                        model: HeapTree::Node(node, value, left_model, middle_model)
                    }, { left: l, right: m });
                    let rotated = fold(tree_at(result), {
                        model: HeapTree::Node(pivot_node, pivot_value,
                            HeapTree::Node(node, value, left_model, middle_model), far_right_model)
                    }, { left: lower, right: z });
                    have rotated.model == heap_rotate_left(old(t.model)) by {
                        rewrite(old(t.model) == HeapTree::Node(node, value, left_model, right_model));
                        rewrite(right_model == HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model));
                        unfold(heap_rotate_left(HeapTree::Node(node, value, left_model,
                            HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model))));
                        normalize();
                    }
                    simp();
                },
            }
        },
    }
}
```

```expect
pass
```
