# either direct tree child is structurally smaller

```c filename=c_decreases_resource_tree_child.c
struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 leftmost_zero(struct node* node) {
    struct node* left;
    int32 result;
    left = node->left;
    if (left == 0) {
        return node->value;
    }
    result = leftmost_zero(left);
    return result;
}
```

```click
resource zero_tree(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->left;
        owns node->right;
        fact node->value == 0;
        contains zero_tree(node->left);
        contains zero_tree(node->right);
    }
}

verifying "c_decreases_resource_tree_child.c";

int32 leftmost_zero(struct node* node) {
    decreases resource zero_tree(node);
    requires node != 0;
    views zero_tree(node);
    immutable;

    ensures result == 0;
} by {
    observe(zero_tree(node));
    if node->left == 0 {
        execute();
        frame();
        simp();
    } else {
        execute();
        frame();
        simp();
    }
}
```

```expect
pass
```
