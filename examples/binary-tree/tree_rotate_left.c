struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

struct node* tree_rotate_left(struct node* node) {
    struct node* pivot;
    struct node* middle;
    pivot = node->right;
    middle = pivot->left;
    node->right = middle;
    pivot->left = node;
    return pivot;
}
