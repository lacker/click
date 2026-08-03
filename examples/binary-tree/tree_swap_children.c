struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 tree_swap_children(struct node* node) {
    struct node* left;
    left = node->left;
    node->left = node->right;
    node->right = left;
    return node->value;
}
