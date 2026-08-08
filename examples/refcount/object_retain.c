struct object {
    int32 refs;
};

void object_retain(struct object* obj) {
    obj->refs = obj->refs + 1;
}
