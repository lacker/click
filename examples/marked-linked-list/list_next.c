struct node {
    int32 value;
    unsigned long word;
};

struct node *list_next(struct node *node) {
    return (struct node *)(node->word & ~1);
}
