struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 tree_make_root(
    struct node* node,
    int32 value,
    struct node* left,
    struct node* right
) {
    node->value = value;
    node->left = left;
    node->right = right;
    return value;
}
