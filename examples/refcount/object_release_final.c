struct object {
    int32 refs;
};

void object_release_final(struct object* obj) {
    obj->refs = 0;
    free(obj);
}
