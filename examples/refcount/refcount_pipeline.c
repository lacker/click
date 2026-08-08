struct object {
    int32 refs;
};

int32 refcount_pipeline() {
    struct object* obj = malloc(sizeof(struct object));
    if (obj == 0) {
        return -1;
    }
    object_init(obj);
    object_retain(obj);
    object_release_nonfinal(obj);
    object_release_final(obj);
    return 0;
}
