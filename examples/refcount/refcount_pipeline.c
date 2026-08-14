struct object {
    int32 refs;
};

int32 refcount_pipeline(int32 amount) {
    struct object* obj = malloc(sizeof(struct object));
    if (obj == 0) {
        return -1;
    }
    object_init(obj);
    object_retain_many(obj, amount);
    object_release_many_nonfinal(obj, amount);
    object_release_final(obj);
    return 0;
}
