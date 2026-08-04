struct node {
    int32 value;
    struct node *next;
};

int32 list_destroy(struct node *node) {
    if (node == 0) {
        return 0;
    }
    struct node *next = node->next;
    int32 destroyed = list_destroy(next);
    free(node);
    return 0;
}
