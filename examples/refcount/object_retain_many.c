struct object {
    int32 refs;
};

void object_retain_many(struct object* obj, int32 amount) {
    obj->refs = obj->refs + amount;
}
