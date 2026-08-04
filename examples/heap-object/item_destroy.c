struct item {
    int32 value;
    struct item *next;
};

int32 item_destroy(struct item *item) {
    free(item);
    return 0;
}
