struct node {
    int32 value;
    struct node* left;
    struct node* right;
};

struct node* tree_empty() {
    return 0;
}
