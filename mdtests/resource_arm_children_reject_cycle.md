# mutually containing resources stay rejected

A matched arm may own another family, but two definitions that own each other
are still a composite resource cycle.

```c filename=resource_arm_children_reject_cycle.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

void empty(struct tree_node *node) {}
```

```click
verifying "resource_arm_children_reject_cycle.c";

spec enum Up {
    UpTop,
    UpNext(Down),
}

spec enum Down {
    DownTop,
    DownNext(Up),
}

resource up_at(node: struct tree_node*) {
    field model: Up;
    match model {
        Up::UpTop => {},
        Up::UpNext(down_model) => {
            owns node->left;
            owns down: down_at(node->left);
            fact node != 0;
            fact down.model == down_model;
        },
    }
}

resource down_at(node: struct tree_node*) {
    field model: Down;
    match model {
        Down::DownTop => {},
        Down::DownNext(up_model) => {
            owns node->right;
            owns up: up_at(node->right);
            fact node != 0;
            fact up.model == up_model;
        },
    }
}

void empty(struct tree_node* node) {
    requires node != 0;
    ensures node != 0;
} by {
    execute();
    simp();
}
```

```expect
fail: composite resource cycle
```
