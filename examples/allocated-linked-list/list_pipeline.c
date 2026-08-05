struct node {
    int32 value;
    struct node *next;
};

int32 list_pipeline(int32 first, int32 second) {
    struct node *list = list_empty();
    list = list_prepend(first, list);
    list = list_prepend(second, list);
    if (list != 0) {
        list_head(list);
        list = list_drop_front(list);
    }
    list_destroy(list);
    return 0;
}
