struct item {
    int32 value;
    struct item *next;
};

struct item *item_create(int32 value) {
    struct item *item = malloc(sizeof(struct item));
    if (item == 0) {
        return 0;
    }
    item->value = value;
    item->next = 0;
    return item;
}
