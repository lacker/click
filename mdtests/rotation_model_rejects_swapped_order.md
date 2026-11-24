# A rotation that swaps two nodes in the in-order sequence cannot claim the rotated model

The negative of `mdtests/rotation_model_preserved.md`, and the one the model
is really for. This rotation keeps every node and every subtree exactly once,
so its result is a perfectly good binary tree and folds without complaint: the
pivot ends up with the far-right subtree on its left and the old root on its
right. What it does not do is preserve the in-order sequence, which now reads
the far-right subtree and the pivot before the root instead of after it.

The proof therefore folds the tree the C actually built, naming the honest
children, and fails only at the `have` that would state the rotated model.
Ownership alone cannot catch this: the claim that is false is the model
equation, and that is exactly where the proof stops.

```c filename=rotation_model_rejects_swapped_order.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

struct tree_node *rotate_left(struct tree_node *root) {
    struct tree_node *pivot;
    struct tree_node *middle;
    struct tree_node *far;

    pivot = root->right;
    middle = pivot->left;
    far = pivot->right;
    root->right = middle;
    pivot->left = far;
    pivot->right = root;
    return pivot;
}
```

```click
verifying "rotation_model_rejects_swapped_order.c";

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
                rewrite(t.model, HeapTree::Node(node, value, left_model, right_model));
                unfold(heap_right(HeapTree::Node(node, value, left_model, right_model)));
                normalize();
            }
            have right_model != HeapTree::Empty by {
                rewrite(right_model, heap_right(t.model));
                close();
            }
            match right_model {
                HeapTree::Empty => { contradiction(right_model == HeapTree::Empty); },
                HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model) => {
                    let { left: l, right: r } = unfold(t);
                    let { left: m, right: z } = unfold(r);
                    step_until(function.exit);
                    have separate(memory(root->left), memory(root->right)) by { close(); }
                    have separate(statement(6).footprint, memory(root->left)) by {
                        normalize() using { separate(memory(root->left), memory(root->right)); };
                    }
                    have at(statement(6).exit, root->left) == at(statement(6).entry, root->left) by {
                        preserve(memory(root->left), statement(6));
                    }
                    have separate(memory(root->left), memory(result->left)) by { close(); }
                    have separate(statement(7).footprint, memory(root->left)) by {
                        normalize() using { separate(memory(root->left), memory(result->left)); };
                    }
                    have at(statement(7).exit, root->left) == at(statement(7).entry, root->left) by {
                        preserve(memory(root->left), statement(7));
                    }
                    have separate(memory(root->left), memory(result->right)) by { close(); }
                    have separate(statement(8).footprint, memory(root->left)) by {
                        normalize() using { separate(memory(root->left), memory(result->right)); };
                    }
                    have at(statement(8).exit, root->left) == at(statement(8).entry, root->left) by {
                        preserve(memory(root->left), statement(8));
                    }
                    have root->left == old(root->left) by {
                        rewrite(at(statement(8).exit, root->left), at(statement(8).entry, root->left));
                        rewrite(at(statement(7).exit, root->left), at(statement(7).entry, root->left));
                        rewrite(at(statement(6).exit, root->left), at(statement(6).entry, root->left));
                        close();
                    }
                    have at(statement(6).exit, root->right) == old(root->right->left) by { close(); }
                    have separate(memory(root->right), memory(result->left)) by { close(); }
                    have separate(statement(7).footprint, memory(root->right)) by {
                        normalize() using { separate(memory(root->right), memory(result->left)); };
                    }
                    have at(statement(7).exit, root->right) == at(statement(7).entry, root->right) by {
                        preserve(memory(root->right), statement(7));
                    }
                    have separate(memory(root->right), memory(result->right)) by { close(); }
                    have separate(statement(8).footprint, memory(root->right)) by {
                        normalize() using { separate(memory(root->right), memory(result->right)); };
                    }
                    have at(statement(8).exit, root->right) == at(statement(8).entry, root->right) by {
                        preserve(memory(root->right), statement(8));
                    }
                    have root->right == old(root->right->left) by {
                        rewrite(at(statement(8).exit, root->right), at(statement(8).entry, root->right));
                        rewrite(at(statement(7).exit, root->right), at(statement(7).entry, root->right));
                        close();
                    }
                    let lower = fold(tree_at(root), {
                        model: HeapTree::Node(node, value, left_model, middle_model),
                        left: l, right: m
                    });
                    let rotated = fold(tree_at(result), {
                        model: HeapTree::Node(pivot_node, pivot_value, far_right_model,
                            HeapTree::Node(node, value, left_model, middle_model)),
                        left: z, right: lower
                    });
                    have rotated.model == heap_rotate_left(old(t.model)) by {
                        rewrite(old(t.model), HeapTree::Node(node, value, left_model, right_model));
                        rewrite(right_model, HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model));
                        unfold(heap_rotate_left(HeapTree::Node(node, value, left_model,
                            HeapTree::Node(pivot_node, pivot_value, middle_model, far_right_model))));
                        normalize();
                    }
                    close();
                },
            }
        },
    }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
