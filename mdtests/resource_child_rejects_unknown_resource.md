# a matched-arm child must name a declared resource

A child may own another family, but only one that is declared.

```c filename=resource_child_rejects_unknown_resource.c
struct tree_node {
    int value;
    struct tree_node *left;
    struct tree_node *right;
};

void empty(struct tree_node *node) {}
```

```click
verifying "resource_child_rejects_unknown_resource.c";

spec enum Context {
    Top,
    Left(struct tree_node*, Context),
}

resource ctx_at(node: struct tree_node*) {
    field model: Context;
    match model {
        Context::Top => {},
        Context::Left(up_node, up_model) => {
            owns node->right;
            owns right: tree_at(node->right);
            owns up: ctx_at(up_node);
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
fail: unknown resource `tree_at`
```
