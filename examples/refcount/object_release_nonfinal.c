struct object {
    int32 refs;
};

void object_release_nonfinal(struct object* obj) {
    obj->refs = obj->refs - 1;
}
