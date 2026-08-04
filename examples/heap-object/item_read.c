struct item {
    int32 value;
    struct item *next;
};

int32 item_read(struct item *item) {
    return item->value;
}
