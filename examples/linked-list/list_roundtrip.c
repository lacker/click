struct node {
    int32 value;
    struct node* next;
};

int32 list_roundtrip(
    struct node* node,
    int32 value,
    struct node* tail
) {
    int32 pushed;
    int32 popped;
    int32 observed;
    pushed = list_push_front(node, value, tail);
    observed = list_head(node);
    popped = list_pop_front(node);
    return observed;
}
