#include "modeled_binary_tree.h"

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

struct tree_node *tree_leftmost(struct tree_node *root) {
    if (root == 0) {
        return 0;
    }

    while (root->left != 0) {
        root = root->left;
    }

    return root;
}

struct tree_node *tree_rightmost(struct tree_node *root) {
    if (root == 0) {
        return 0;
    }

    while (root->right != 0) {
        root = root->right;
    }

    return root;
}

int tree_contains(struct tree_node *root, struct tree_node *target) {
    if (root == 0) {
        return 0;
    }
    if (root == target) {
        return 1;
    }
    if (tree_contains(root->left, target)) {
        return 1;
    }
    return tree_contains(root->right, target);
}

struct tree_node *tree_rotate_left(struct tree_node *root) {
    struct tree_node *pivot;
    struct tree_node *middle;

    pivot = root->right;
    middle = pivot->left;
    root->right = middle;
    pivot->left = root;
    return pivot;
}

struct tree_node *tree_rotate_right(struct tree_node *root) {
    struct tree_node *pivot;
    struct tree_node *middle;

    pivot = root->left;
    middle = pivot->right;
    root->left = middle;
    pivot->right = root;
    return pivot;
}
