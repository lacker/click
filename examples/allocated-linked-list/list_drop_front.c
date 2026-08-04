struct node {
    int32 value;
    struct node *next;
};

struct node *list_drop_front(struct node *node) {
    struct node *next = node->next;
    free(node);
    return next;
}
