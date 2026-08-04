struct node {
    int32 value;
    struct node *next;
};

int32 list_head(struct node *node) {
    return node->value;
}
