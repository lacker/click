struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 tree_sum_root_and_children(struct node* node) {
    int32 sum;
    sum = node->value + node->left->value;
    return sum + node->right->value;
}
