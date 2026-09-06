struct node {
    int32 value;
    unsigned long word;
};

uint32 list_count_live(struct node *node) {
    if (node == 0) {
        return 0;
    }
    uint32 rest = list_count_live((struct node *)(node->word & ~1));
    if ((node->word & 1) != 0) {
        return rest;
    }
    return rest + 1;
}
