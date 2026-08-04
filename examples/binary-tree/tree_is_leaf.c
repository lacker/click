struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 tree_is_leaf(struct node* node) {
    if (node->left != 0) {
        return 0;
    }
    if (node->right != 0) {
        return 0;
    }
    return 1;
}
