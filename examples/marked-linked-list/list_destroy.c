struct node {
    int32 value;
    unsigned long word;
};

void list_destroy(struct node *node) {
    if (node == 0) {
        return;
    }
    struct node *next = (struct node *)(node->word & ~1);
    list_destroy(next);
    free(node);
}
