struct node {
    int32 value;
    unsigned long word;
};

void list_mark(struct node *node) {
    node->word = node->word | 1;
}
