resource tree(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->left;
        owns node->right;
        contains tree(node->left);
        contains tree(node->right);
    }
}

verifying "tree_empty.c";
verifying "tree_root.c";
verifying "tree_make_root.c";
verifying "tree_swap_children.c";
verifying "tree_leaf_pipeline.c";
verifying "tree_is_leaf.c";

struct node* tree_empty() {
    produces tree(result);

    ensures result == 0;
} by {
    execute();
    fold(tree(result));
    simp();
}

int32 tree_root(struct node* node) {
    requires node != 0;
    owns tree(node);
    immutable;

    ensures result == node->value;
} by {
    unfold(tree(node));
    execute();
    fold(tree(node));
    frame();
    simp();
}

int32 tree_make_root(
    struct node* node,
    int32 value,
    struct node* left,
    struct node* right
) {
    requires node != 0;
    consumes node->value;
    consumes node->left;
    consumes node->right;
    consumes tree(left);
    consumes tree(right);
    mutable node->value, node->left, node->right;
    produces tree(node);

    ensures result == value;
    ensures node->value == value;
    ensures node->left == left;
    ensures node->right == right;
} by {
    execute();
    fold(tree(node));
    frame();
    simp();
}

int32 tree_swap_children(struct node* node) {
    requires node != 0;
    consumes tree(node);
    mutable node->left, node->right;
    produces tree(node);

    ensures result == old(node->value);
    ensures node->value == old(node->value);
    ensures node->left == old(node->right);
    ensures node->right == old(node->left);
} by {
    unfold(tree(node));
    execute();
    fold(tree(node));
    frame();
    simp();
}

int32 tree_leaf_pipeline(struct node* node, int32 value) {
    requires node != 0;
    consumes node->value;
    consumes node->left;
    consumes node->right;
    mutable node->value, node->left, node->right;
    produces tree(node);

    ensures result == value;
    ensures node->value == value;
} by {
    execute();
    frame();
    simp();
}

int32 tree_is_leaf(struct node* node) {
    requires node != 0;
    views tree(node);
    immutable;

    ensures result == 1 implies node->left == 0;
    ensures result == 1 implies node->right == 0;
    ensures node->left != 0 implies result == 0;
    ensures node->left == 0 implies (node->right != 0 implies result == 0);
    ensures node->left == 0 implies (node->right == 0 implies result == 1);
    ensures result == 0 or result == 1;
} by {
    observe(tree(node));
    execute();
    frame();
    simp();
}
