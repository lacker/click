# A concrete execution theorem carries a modeled tree instance

The target contract and the implementation each declare one instance of the
same modeled resource under different names. The conclusion's `as` map
introduces the target's instance as `r`, and the call step binds the callee's
own binder `t` to that same `r`, so the two vocabularies meet in one name the
theorem introduced.

```c filename=c_contract_executes_concrete_model.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

void touch(struct tree_node *node) { }

int accept(void (*callback)(struct tree_node*)) { return 0; }

int caller() { return accept(&touch); }
```

```click
verifying "c_contract_executes_concrete_model.c";

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

contract Preserve(root: tree_at(node)) for void(struct tree_node* node) {
    owns root;
    ensures root.model == old(root.model);
}

void touch(struct tree_node* node) {
    owns t: tree_at(node);
    ensures t.model == old(t.model);
} by {
    execute();
    simp();
}

theorem touch_preserves() executes touch(struct tree_node* node) {
    ensures Preserve(&touch) as { root: r } by {
        step(touch(node), { t: r });
        simp();
    }
}

int accept(void (*callback)(struct tree_node*)) {
    requires Preserve(callback);
    ensures result == 0;
} by {
    execute();
    simp();
}

int caller() {
    ensures result == 0;
} by {
    apply(touch_preserves());
    execute();
    simp();
}
```

```expect
pass
```
