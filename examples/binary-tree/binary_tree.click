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
    owns tree(node);
    immutable;

    ensures result == node->value;
} by {
    unfold(tree(node));
    step() using {
        node != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(node[0..2]);
        loadable((node + 2)[0..2]);
        loadable((node + 4)[0..2]);
    }
    fold(tree(node));
    frame();
    have result == node->value by {
        normalize();
    }
    assumption();
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
    mutable node->value, node->left, node->right;
    produces tree(node);

    ensures result == value;
    ensures node->value == value;
    ensures node->left == left;
    ensures node->right == right;
} by {
    step() using {
        node != 0;
        loadable(node[0..2]);
        loadable((node + 2)[0..2]);
        loadable((node + 4)[0..2]);
    }
    step() using {
        node != 0;
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        node != 0;
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        node != 0;
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    fold(tree(node));
    frame();
    have result == value by {
        normalize();
    }
    have node->value == value by {
        normalize();
    }
    have node->left == left by {
        normalize();
    }
    have node->right == right by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
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
    step() using {
        node != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(node[0..2]);
        loadable((node + 2)[0..2]);
        loadable((node + 4)[0..2]);
    }
    step() using {
        node != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        node != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        node != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        node != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    fold(tree(node));
    frame();
    have result == old(node->value) by {
        normalize();
    }
    have node->value == old(node->value) by {
        normalize();
    }
    have node->left == old(node->right) by {
        normalize();
    }
    have node->right == old(node->left) by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
    assumption();
    assumption();
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
    step() using {
        node != 0;
        loadable(node[0..2]);
        loadable((node + 2)[0..2]);
        loadable((node + 4)[0..2]);
    }
    step() using {
        node != 0;
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        node != 0;
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        node != 0;
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        node != 0;
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    have left == 0 by {
        assumption();
    }
    step() using {
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
        left == 0;
    }
    have right == 0 by {
        assumption();
    }
    step() using {
        node != 0;
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
        left == 0;
        right == 0;
    }
    have node->right == right by {
        assumption();
    }
    have node->left == left by {
        assumption();
    }
    have made == value by {
        assumption();
    }
    step() using {
        node != 0;
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        left == 0;
        right == 0;
        made == value;
        node->value == value;
        node->left == left;
        node->right == right;
    }
    have swapped == node->value by {
        assumption();
    }
    step() using {
        node != 0;
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        left == 0;
        right == 0;
        made == value;
        swapped == node->value;
        node->left == at(statement(8).entry, node->right);
        node->right == at(statement(8).entry, node->left);
        at(statement(8).exit, node->value) == at(statement(8).exit, value);
    }
    have observed == node->value by {
        assumption();
    }
    step() using {
        node != 0;
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        left == 0;
        right == 0;
        made == value;
        swapped == node->value;
        node->left == at(statement(8).entry, node->right);
        node->right == at(statement(8).entry, node->left);
        at(statement(8).exit, node->value) == at(statement(8).exit, value);
        observed == node->value;
    }
    frame() using {
    }
    have result == value by {
        rewrite(at(statement(10).entry, observed) == at(statement(10).entry, node->value));
        assumption();
    }
    have node->value == value by {
        assumption();
    }
    have node->left == 0 by {
        rewrite(node->left == at(statement(8).entry, node->right));
        rewrite(at(statement(8).entry, node->right) == at(statement(8).entry, right));
        assumption();
    }
    have node->right == 0 by {
        rewrite(node->right == at(statement(8).entry, node->left));
        rewrite(at(statement(8).entry, node->left) == at(statement(8).entry, left));
        assumption();
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
    if at(function.entry, node->left) != at(function.entry, 0) {
        step() using {
            separate(memory(node->value), memory(node->left));
            separate(memory(node->value), memory(node->right));
            separate(memory(node->left), memory(node->right));
            separate(tree(node->left), tree(node->right));
            separate(memory(node->value), tree(node->left));
            separate(memory(node->value), tree(node->right));
            separate(memory(node->left), tree(node->left));
            separate(memory(node->left), tree(node->right));
            separate(memory(node->right), tree(node->left));
            separate(memory(node->right), tree(node->right));
            loadable(node->value);
            loadable(node->left);
            loadable(node->right);
        }
        step() using {
            node != 0;
            separate(memory(node->value), memory(node->left));
            separate(memory(node->value), memory(node->right));
            separate(memory(node->left), memory(node->right));
            separate(tree(node->left), tree(node->right));
            separate(memory(node->value), tree(node->left));
            separate(memory(node->value), tree(node->right));
            separate(memory(node->left), tree(node->left));
            separate(memory(node->left), tree(node->right));
            separate(memory(node->right), tree(node->left));
            separate(memory(node->right), tree(node->right));
            loadable(node->value);
            loadable(node->left);
            loadable(node->right);
            at(function.entry, node->left) != at(function.entry, 0);
        }
    } else {
        step() using {
            separate(memory(node->value), memory(node->left));
            separate(memory(node->value), memory(node->right));
            separate(memory(node->left), memory(node->right));
            separate(tree(node->left), tree(node->right));
            separate(memory(node->value), tree(node->left));
            separate(memory(node->value), tree(node->right));
            separate(memory(node->left), tree(node->left));
            separate(memory(node->left), tree(node->right));
            separate(memory(node->right), tree(node->left));
            separate(memory(node->right), tree(node->right));
            loadable(node->value);
            loadable(node->left);
            loadable(node->right);
        }
        step() using {
            node != 0;
            separate(memory(node->value), memory(node->left));
            separate(memory(node->value), memory(node->right));
            separate(memory(node->left), memory(node->right));
            separate(tree(node->left), tree(node->right));
            separate(memory(node->value), tree(node->left));
            separate(memory(node->value), tree(node->right));
            separate(memory(node->left), tree(node->left));
            separate(memory(node->left), tree(node->right));
            separate(memory(node->right), tree(node->left));
            separate(memory(node->right), tree(node->right));
            loadable(node->value);
            loadable(node->left);
            loadable(node->right);
            at(function.entry, node->left) == at(function.entry, 0);
        }
        if at(function.entry, node->right) != at(function.entry, 0) {
            step() using {
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(node->value);
                loadable(node->left);
                loadable(node->right);
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(node->value);
                loadable(node->left);
                loadable(node->right);
                at(function.entry, node->left) == at(function.entry, 0);
                at(function.entry, node->right) != at(function.entry, 0);
            }
        } else {
            step() using {
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(node->value);
                loadable(node->left);
                loadable(node->right);
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(node->value);
                loadable(node->left);
                loadable(node->right);
                at(function.entry, node->left) == at(function.entry, 0);
                at(function.entry, node->right) == at(function.entry, 0);
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(node->value);
                loadable(node->left);
                loadable(node->right);
                at(function.entry, node->left) == at(function.entry, 0);
                at(function.entry, node->right) == at(function.entry, 0);
            }
        }
    }
    frame();
    if at(function.entry, node->left) != at(function.entry, 0) {
        have result == 1 implies node->left == 0 by {
            normalize();
        }
        have result == 1 implies node->right == 0 by {
            normalize();
        }
        have node->left != 0 implies result == 0 by {
            normalize();
        }
        have node->left == 0 implies node->right != 0 implies result == 0 by {
            normalize();
        }
        have node->left == 0 implies node->right == 0 implies result == 1 by {
            intro();
            contradiction(node->left != 0);
        }
        have result == 0 or result == 1 by {
            normalize();
        }
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
        assumption();
    } else {
        if at(function.entry, node->right) != at(function.entry, 0) {
            have result == 1 implies node->left == 0 by {
                normalize();
            }
            have result == 1 implies node->right == 0 by {
                normalize();
            }
            have node->left != 0 implies result == 0 by {
                normalize();
            }
            have node->left == 0 implies node->right != 0 implies result == 0 by {
                normalize();
            }
            have node->left == 0 implies node->right == 0 implies result == 1 by {
                intro();
                intro();
                contradiction(node->right != 0);
            }
            have result == 0 or result == 1 by {
                normalize();
            }
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
            assumption();
        } else {
            have result == 1 implies node->left == 0 by {
                rewrite(node->left == 0);
                normalize();
            }
            have result == 1 implies node->right == 0 by {
                rewrite(node->right == 0);
                normalize();
            }
            have node->left != 0 implies result == 0 by {
                intro();
                contradiction(node->left == 0);
            }
            have node->left == 0 implies node->right != 0 implies result == 0 by {
                intro();
                intro();
                contradiction(node->right == 0);
            }
            have node->left == 0 implies node->right == 0 implies result == 1 by {
                normalize();
            }
            have result == 0 or result == 1 by {
                normalize();
            }
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
    frame() using {
    }
    have result == ((node->value + node->left->value) + node->right->value) by {
        normalize();
    }
    assumption();
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
    step() using {
        node != 0;
        node->right != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        node != 0;
        node->right != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        node != 0;
        node->right != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
    }
    step() using {
        node != 0;
        node->right != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
        separate(memory(node->right[0..2]), memory(node->right[2..4]));
        separate(memory(node->right[0..2]), memory(node->right[4..6]));
        separate(memory(node->right[2..4]), memory(node->right[4..6]));
    }
    step() using {
        node != 0;
        node->right != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
        separate(memory(node->right[0..2]), memory(node->right[2..4]));
        separate(memory(node->right[0..2]), memory(node->right[4..6]));
        separate(memory(node->right[2..4]), memory(node->right[4..6]));
    }
    step() using {
        node != 0;
        pivot != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
        separate(memory(node->right[0..2]), memory(node->right[2..4]));
        separate(memory(node->right[0..2]), memory(node->right[4..6]));
        separate(memory(node->right[2..4]), memory(node->right[4..6]));
    }
    step() using {
        node != 0;
        pivot != 0;
        separate(memory(node[0..2]), memory(node[2..4]));
        separate(memory(node[0..2]), memory(node[4..6]));
        separate(memory(node[2..4]), memory(node[4..6]));
        loadable(old(node[0..2]));
        loadable(old((node + 2)[0..2]));
        loadable(old((node + 4)[0..2]));
        separate(memory(node->right[0..2]), memory(node->right[2..4]));
        separate(memory(node->right[0..2]), memory(node->right[4..6]));
        separate(memory(node->right[2..4]), memory(node->right[4..6]));
    }
    fold(tree(node));
    fold(tree(result));
    frame() using {
    }
    have result == old(node->right) by {
        normalize();
    }
    have result->left == node by {
        normalize();
    }
    assumption();
    assumption();
    assumption();
}

int32 tree_walk(struct node* node) {
    decreases resource tree(node);
    requires node != 0;
    views tree(node);
    immutable;

    ensures result == node->value;
} by {
    observe(tree(node));
    if node->left == 0 {
        if node->right == 0 {
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(node->value);
                loadable(node->left);
                loadable(node->right);
                node->left == 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                contains(tree(node), memory(node->value));
                contains(tree(node), memory(node->left));
                contains(tree(node), memory(node->right));
                contains(tree(node), tree(node->left));
                contains(tree(node), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                contains(tree(node), memory(node->value));
                contains(tree(node), memory(node->left));
                contains(tree(node), memory(node->right));
                contains(tree(node), tree(node->left));
                contains(tree(node), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right == 0;
            }
            frame() using {
            }
            have result == node->value by {
                normalize();
            }
            assumption();
        } else {
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(node->value);
                loadable(node->left);
                loadable(node->right);
                node->left == 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                contains(tree(node), memory(node->value));
                contains(tree(node), memory(node->left));
                contains(tree(node), memory(node->right));
                contains(tree(node), tree(node->left));
                contains(tree(node), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                contains(tree(node), memory(node->value));
                contains(tree(node), memory(node->left));
                contains(tree(node), memory(node->right));
                contains(tree(node), tree(node->left));
                contains(tree(node), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right != 0;
            }
            have child_value == node->right[0] by {
                assumption();
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left == 0;
                node->right != 0;
                at(statement(13).entry, child_value) == at(statement(13).entry, node->right[0]);
            }
            frame() using {
            }
            have result == node->value by {
                normalize();
            }
            assumption();
        }
    } else {
        if node->right == 0 {
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(node->value);
                loadable(node->left);
                loadable(node->right);
                node->left != 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                contains(tree(node), memory(node->value));
                contains(tree(node), memory(node->left));
                contains(tree(node), memory(node->right));
                contains(tree(node), tree(node->left));
                contains(tree(node), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right == 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right == 0;
            }
            have child_value == node->left[0] by {
                assumption();
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                contains(tree(node), memory(node->value));
                contains(tree(node), memory(node->left));
                contains(tree(node), memory(node->right));
                contains(tree(node), tree(node->left));
                contains(tree(node), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right == 0;
                at(statement(10).entry, child_value) == at(statement(10).entry, node->left[0]);
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right == 0;
                at(statement(10).entry, child_value) == at(statement(10).entry, node->left[0]);
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right == 0;
                at(statement(10).entry, child_value) == at(statement(10).entry, node->left[0]);
            }
            frame() using {
            }
            have result == node->value by {
                normalize();
            }
            assumption();
        } else {
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(node->value);
                loadable(node->left);
                loadable(node->right);
                node->left != 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                contains(tree(node), memory(node->value));
                contains(tree(node), memory(node->left));
                contains(tree(node), memory(node->right));
                contains(tree(node), tree(node->left));
                contains(tree(node), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right != 0;
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right != 0;
            }
            have child_value == node->left[0] by {
                assumption();
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                contains(tree(node), memory(node->value));
                contains(tree(node), memory(node->left));
                contains(tree(node), memory(node->right));
                contains(tree(node), tree(node->left));
                contains(tree(node), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right != 0;
                at(statement(10).entry, child_value) == at(statement(10).entry, node->left[0]);
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right != 0;
                at(statement(10).entry, child_value) == at(statement(10).entry, node->left[0]);
            }
            have child_value == node->right[0] by {
                assumption();
            }
            step() using {
                node != 0;
                separate(memory(node->value), memory(node->left));
                separate(memory(node->value), memory(node->right));
                separate(memory(node->left), memory(node->right));
                separate(tree(node->left), tree(node->right));
                separate(memory(node->value), tree(node->left));
                separate(memory(node->value), tree(node->right));
                separate(memory(node->left), tree(node->left));
                separate(memory(node->left), tree(node->right));
                separate(memory(node->right), tree(node->left));
                separate(memory(node->right), tree(node->right));
                loadable(old(node->value));
                loadable(old(node->left));
                loadable(old(node->right));
                node->left != 0;
                node->right != 0;
                at(statement(10).entry, child_value) == at(statement(10).entry, node->left[0]);
                at(statement(13).entry, child_value) == at(statement(13).entry, node->right[0]);
            }
            frame() using {
            }
            have result == node->value by {
                normalize();
            }
            assumption();
        }
    }
}
