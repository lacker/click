# a structural loop measure refuses a back edge that leaves the tree

`decreases sub;` on a loop names the loop's own resource binder, so the
instance the binder ends holding must be a direct contained child, in the
exact resource definition, of the instance it held at the loop head. This body
moves the cursor to a node of an unrelated tree the contract also owns. The
other tree is not one of the loop's own resources, so the body never holds it:
the back edge has no `tree_at` at the new cursor at all and refuses by naming
the binder. A descent argument needs the binder to end on a submodel of what
it started with, and an unrelated node is not reachable that way even when the
enclosing frame owns it.

Its sibling negative, a back edge that keeps the same instance, is
`mdtests/loop_decreases_rejects_same_instance.md`.

```c filename=loop_decreases_rejects_unrelated_node.c
struct tree_node {
    int32 value;
    struct tree_node *left;
    struct tree_node *right;
};

void walk(struct tree_node *root, struct tree_node *other) {
    while (root->left != 0) {
        root = other;
    }
}
```

```click
verifying "loop_decreases_rejects_unrelated_node.c";

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

void walk(struct tree_node* root, struct tree_node* other) {
    owns t: tree_at(root);
    owns o: tree_at(other);
    requires t.model != HeapTree::Empty;
    requires o.model != HeapTree::Empty;
} by {
    loop {
        owns t: tree_at(root);
        decreases t;
        invariant t.model != HeapTree::Empty;

        initialize by simp;
        preserve by {
            match t.model {
                HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
                HeapTree::Node(identity, value, left_model, right_model) => {
                    step();
                    close_invariants();
                },
            }
        }
    }
    simp();
}
```

```expect
fail: loop binder `t` has no owned `tree_at` instance at its arguments here
```
