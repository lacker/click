struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 tree_root(struct node* node) {
    return node->value;
}
