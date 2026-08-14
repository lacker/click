struct object {
    int32 refs;
};

void object_release_many_nonfinal(struct object* obj, int32 amount) {
    obj->refs = obj->refs - amount;
}
