struct node {
    int32 value;
    struct node* next;
};

int32 zero_list_push(struct node* node, struct node* tail) {
    node->value = 0;
    node->next = tail;
    return 0;
}
