struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

int32 tree_leaf_pipeline(struct node* node, int32 value) {
    struct node* left;
    struct node* right;
    int32 made;
    int32 swapped;
    int32 observed;
    left = tree_empty();
    right = tree_empty();
    made = tree_make_root(node, value, left, right);
    swapped = tree_swap_children(node);
    observed = tree_root(node);
    return observed;
}
