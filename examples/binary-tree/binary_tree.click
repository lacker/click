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
verifying "tree_sum_root_and_children.c";
verifying "tree_rotate_left.c";

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
    ensures node->left == 0;
    ensures node->right == 0;
} by {
    execute();
    frame();
    have result == value by {
        derive using {
            at(statement(10).entry, observed) == at(statement(10).entry, node->value);
            at(statement(10).entry, node->value) == at(statement(10).entry, value);
        }
    }
    have node->value == value by {
        assumption();
    }
    have node->left == 0 by {
        derive using {
            node->left == at(statement(8).entry, node->right);
            at(statement(8).entry, node->right) == at(statement(8).entry, right);
            at(statement(10).entry, right) == at(statement(10).entry, 0);
        }
    }
    have node->right == 0 by {
        derive using {
            node->right == at(statement(8).entry, node->left);
            at(statement(8).entry, node->left) == at(statement(8).entry, left);
            at(statement(10).entry, left) == at(statement(10).entry, 0);
        }
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
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
    immutable;

    ensures result == node->value + node->left->value + node->right->value;
} by {
    observe(tree(node));
    observe(tree(node->left));
    observe(tree(node->right));
    step() using {}
    step() using {
        0 <= node->value;
        node->value <= 715827882;
        0 <= node->left->value;
        node->left->value <= 715827882;
        loadable(node->value);
        loadable(node->left->value);
    }
    step() using {
        0 <= node->value;
        node->value <= 715827882;
        0 <= node->left->value;
        node->left->value <= 715827882;
        0 <= node->right->value;
        node->right->value <= 715827882;
        loadable(node->right->value);
    }
    frame();
    simp();
}

struct node* tree_rotate_left(struct node* node) {
    requires node != 0;
    requires node->right != 0;
    consumes tree(node);
    mutable node->right, node->right->left;
    produces tree(result);

    ensures result == old(node->right);
    ensures result->left == node;
} by {
    unfold(tree(node));
    unfold(tree(node->right));
    execute();
    fold(tree(node));
    fold(tree(result));
    frame();
    simp();
}
