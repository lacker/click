struct object {
    int32 refs;
};

void object_init(struct object* obj) {
    obj->refs = 1;
}
