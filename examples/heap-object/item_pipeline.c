struct item {
    int32 value;
    struct item *next;
};

int32 item_pipeline(int32 value) {
    struct item *item = item_create(value);
    if (item == 0) {
        return -1;
    }
    int32 result = item_read(item);
    int32 destroyed = item_destroy(item);
    return 0;
}
