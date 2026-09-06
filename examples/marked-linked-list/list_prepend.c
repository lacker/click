struct node {
    int32 value;
    unsigned long word;
};

struct node *list_prepend(int32 value, struct node *tail) {
    struct node *node = malloc(sizeof(struct node));
    if (node == 0) {
        return tail;
    }
    node->value = value;
    node->word = (unsigned long)tail;
    return node;
}
