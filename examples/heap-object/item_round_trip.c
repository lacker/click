struct item {
    int32 value;
    struct item *next;
};

int32 item_round_trip(int32 value) {
    struct item *item = malloc(sizeof(struct item));
    if (item == 0) {
        return -1;
    }
    item->value = value;
    item->next = 0;
    int32 result = item->value;
    free(item);
    return result;
}
