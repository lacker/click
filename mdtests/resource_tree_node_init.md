# A resource for stored tree links

The initializer body is the unchanged `tree_node_init` from the modeled tree
example. The resource owns all three fields, including the stored links; an
address in its model is not memory ownership. Empty children may share null,
but child resource instances are independently consumed.

```c filename=resource_tree_node_init.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

void tree_node_init(
    struct tree_node *node,
    int value,
    struct tree_node *left,
    struct tree_node *right
) {
    node->value = value;
    node->left = left;
    node->right = right;
}

int read_value(struct tree_node *node) { return node->value; }
void empty(struct tree_node *p) {}
```

```click
verifying "resource_tree_node_init.c";

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

void tree_node_init(struct tree_node* node, int value,
                    struct tree_node* left, struct tree_node* right) {
    consumes node->value;
    consumes node->left;
    consumes node->right;
    consumes l: tree_at(left);
    consumes r: tree_at(right);
    requires node != 0;
    produces root: tree_at(node);
    ensures root.model == HeapTree::Node(node, value, old(l.model), old(r.model));
} by {
    execute();
    let root = fold(tree_at(node), {
        model: HeapTree::Node(node, value, l.model, r.model)
    }, { left: l, right: r });
    simp();
}

int read_value(struct tree_node* node) {
    owns root: tree_at(node);
    requires root.model == HeapTree::Node(node, 7, HeapTree::Empty, HeapTree::Empty);
    ensures result == 7;
    ensures root.model == old(root.model);
} by {
    unfold(root) as { left: l, right: r };
    execute();
    let root = fold(tree_at(node), { model: old(root.model) }, { left: l, right: r });
    simp();
}

void empty(struct tree_node* p) {
    requires p == 0;
    produces root: tree_at(p);
    ensures root.model == HeapTree::Empty;
} by {
    execute();
    let root = fold(tree_at(p), { model: HeapTree::Empty });
    simp();
}
```

```expect
pass
```
