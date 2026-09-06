struct node {
    int32 value;
    unsigned long word;
};

int32 list_pipeline(int32 first, int32 second) {
    struct node *list = list_empty();
    list = list_prepend(first, list);
    list = list_prepend(second, list);
    if (list != 0) {
        list_mark(list);
    }
    uint32 live = list_count_live(list);
    list_destroy(list);
    return 0;
}
