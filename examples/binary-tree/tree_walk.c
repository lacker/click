struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 tree_walk(struct node* node) {
    int32 value;
    struct node* left;
    struct node* right;
    int32 child_value;

    value = node->value;
    left = node->left;
    right = node->right;
    if (left != 0) {
        child_value = tree_walk(left);
    }
    if (right != 0) {
        child_value = tree_walk(right);
    }
    return value;
}
