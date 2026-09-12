# A rotation that links one subtree into two slots cannot claim the rotated model

The negative of `mdtests/rotation_model_preserved.md`. This rotation links the
old root into both of the pivot's slots instead of only its left one, so one
subtree occupies two positions of the same node and the pivot's own right
subtree is dropped.

The proof script is the positive's, unchanged. The lower node still folds: the
root keeps its left subtree and receives the middle one. The second fold is
where the claim breaks, because `tree_at(result)` owns a separate
`tree_at(p->right)` and `result->right` now names the node the left child
already stands for. Linear ownership refuses the duplication rather than
silently building a tree with a node in it twice; naming the same instance
for both slots is rejected earlier still, as a duplicate child slot.

```c filename=rotation_model_rejects_reused_child.c
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
    pivot->right = root;
    return pivot;
}
```

```click
verifying "rotation_model_rejects_reused_child.c";

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
fail: `rotate_left.contract` proof step checked step 3: selected child does not satisfy the proposed parent model
```
