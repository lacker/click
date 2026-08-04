struct node {
    int32 value;
    struct node* next;
};

int32 zero_list_pipeline(struct node* first, struct node* second) {
    int32 full_sum;
    int32 bounded_sum;
    second->value = 0;
    second->next = 0;
    first->value = 0;
    first->next = second;
    full_sum = zero_list_sum(first);
    bounded_sum = zero_list_sum_bounded(first, 2);
    return full_sum + bounded_sum;
}
