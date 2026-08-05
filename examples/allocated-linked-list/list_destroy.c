struct node {
    int32 value;
    struct node *next;
};

void list_destroy(struct node *node) {
    if (!node) {
        return;
    }
    struct node *next = node->next;
    list_destroy(next);
    free(node);
}
