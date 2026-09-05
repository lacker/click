#ifndef MODELED_BINARY_TREE_H
#define MODELED_BINARY_TREE_H

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
);

struct tree_node *tree_leftmost(struct tree_node *root);
struct tree_node *tree_rightmost(struct tree_node *root);
int tree_contains(struct tree_node *root, struct tree_node *target);
struct tree_node *tree_rotate_left(struct tree_node *root);
struct tree_node *tree_rotate_right(struct tree_node *root);

#endif
