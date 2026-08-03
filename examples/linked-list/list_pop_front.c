struct node {
    int32 value;
    struct node* next;
};

int32 list_pop_front(
    struct node* node
) {
    return node->value;
}
