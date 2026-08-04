struct node {
    int32 value;
    struct node* next;
};

int32 zero_list_sum(struct node* node) {
    struct node* next;
    int32 tail_sum;
    next = node->next;
    if (next == 0) {
        return node->value;
    }
    tail_sum = zero_list_sum(next);
    return tail_sum;
}
