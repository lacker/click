struct node {
    int32 value;
    unsigned long word;
};

int32 list_is_marked(struct node *node) {
    return (node->word & 1) != 0;
}
