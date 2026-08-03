struct node {
    int32 value;
    struct node* next;
};

int32 list_push_front(
    struct node* node,
    int32 value,
    struct node* tail
) {
    node->value = value;
    node->next = tail;
    return value;
}
