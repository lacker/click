resource tree(node: struct node*) {
    if node != 0 {
        owns node->value;
        owns node->left;
        owns node->right;
        owns tree(node->left);
        owns tree(node->right);
    }
}

verifying "tree_empty.c";
verifying "tree_root.c";
verifying "tree_make_root.c";
verifying "tree_swap_children.c";
verifying "tree_leaf_pipeline.c";
verifying "tree_is_leaf.c";
verifying "tree_sum_root_and_children.c";
verifying "tree_rotate_left.c";
verifying "tree_walk.c";

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
    views tree(node);

    ensures result == node->value;
} by {
    observe(tree(node));
    step();
    assumption();
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
    produces tree(node);

    ensures result == value;
    ensures node->value == value;
    ensures node->left == left;
    ensures node->right == right;
} by {
    step();
    step();
    step();
    step();
    fold(tree(node));
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 tree_swap_children(struct node* node) {
    requires node != 0;
    views node->value;
    owns node->left;
    owns node->right;

    ensures result == old(node->value);
    ensures node->value == old(node->value);
    ensures node->left == old(node->right);
    ensures node->right == old(node->left);
} by {
    execute();
    simp();
}

int32 tree_leaf_pipeline(struct node* node, int32 value) {
    requires node != 0;
    consumes node->value;
    consumes node->left;
    consumes node->right;
    produces tree(node);

    ensures result == value;
    ensures node->value == value;
    ensures node->left == 0;
    ensures node->right == 0;
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    unfold(tree(node));
    step();
    fold(tree(node));
    step();
    step();
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
}

int32 tree_is_leaf(struct node* node) {
    requires node != 0;
    views tree(node);

    ensures result == 1 implies node->left == 0;
    ensures result == 1 implies node->right == 0;
    ensures node->left != 0 implies result == 0;
    ensures node->left == 0 implies (node->right != 0 implies result == 0);
    ensures node->left == 0 implies (node->right == 0 implies result == 1);
    ensures result == 0 or result == 1;
} by {
    observe(tree(node));
    if at(function.entry, node->left) != at(function.entry, 0) {
        step();
        step();
    } else {
        step();
        step();
        if at(function.entry, node->right) != at(function.entry, 0) {
            step();
            step();
        } else {
            step();
            step();
            step();
        }
    }
    if at(function.entry, node->left) != at(function.entry, 0) {
        have result == 1 implies node->left == 0 by auto;
        have result == 1 implies node->right == 0 by auto;
        have node->left != 0 implies result == 0 by auto;
        have node->left == 0 implies node->right != 0 implies result == 0 by auto;
        have node->left == 0 implies node->right == 0 implies result == 1 by auto;
        have result == 0 or result == 1 by auto;
 assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
    } else {
        if at(function.entry, node->right) != at(function.entry, 0) {
            have result == 1 implies node->left == 0 by auto;
            have result == 1 implies node->right == 0 by auto;
            have node->left != 0 implies result == 0 by auto;
            have node->left == 0 implies node->right != 0 implies result == 0 by auto;
            have node->left == 0 implies node->right == 0 implies result == 1 by auto;
            have result == 0 or result == 1 by auto;
     assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
        } else {
            have result == 1 implies node->left == 0 by auto;
            have result == 1 implies node->right == 0 by auto;
            have node->left != 0 implies result == 0 by auto;
            have node->left == 0 implies node->right != 0 implies result == 0 by auto;
            have node->left == 0 implies node->right == 0 implies result == 1 by auto;
            have result == 0 or result == 1 by auto;
     assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
        }
    }
}

int32 tree_sum_root_and_children(struct node* node) {
    requires node != 0;
    requires node->left != 0;
    requires node->right != 0;
    requires 0 <= node->value;
    requires node->value <= 715827882;
    requires 0 <= node->left->value;
    requires node->left->value <= 715827882;
    requires 0 <= node->right->value;
    requires node->right->value <= 715827882;
    views tree(node);

    ensures result == node->value + node->left->value + node->right->value;
} by {
    observe(tree(node));
    observe(tree(node->left));
    observe(tree(node->right));
    step();
    step();
    step();
    assumption();
}

struct node* tree_rotate_left(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    consumes tree(node);
    produces tree(result);

    ensures result == old(node->right);
    ensures result->left == node;
} by {
    unfold(tree(node));
    unfold(tree(node->right));
    step();
    step();
    step();
    step();
    step();
    step();
    step();
    fold(tree(node));
    fold(tree(result));
    assumption();
    assumption();
    assumption();
}

int32 tree_walk(struct node* node) {
    decreases tree(node);
    requires node != 0;
    views tree(node);

    ensures result == node->value;
} by {
    observe(tree(node));
    if node->left == 0 {
        if node->right == 0 {
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            assumption();
        } else {
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            assumption();
        }
    } else {
        if node->right == 0 {
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            assumption();
        } else {
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            step();
            assumption();
        }
    }
}
