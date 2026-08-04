struct node {
    int32 value;
    struct node* next;
};

int32 zero_list_sum_bounded(struct node* node, int32 fuel) {
    struct node* next;
    int32 tail_sum;
    next = node->next;
    if (fuel > 0) {
        if (next == 0) {
            return node->value;
        }
        tail_sum = zero_list_sum_bounded(next, fuel - 1);
        return tail_sum;
    }
    return 0;
}
