struct json_object {
    int32 ref_count;
};

int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
    obj->ref_count = count;
    return obj->ref_count;
}
