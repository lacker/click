struct json_object {
    int32 ref_count;
};

int32 json_object_get_ref_count(struct json_object* obj) {
    return obj->ref_count;
}
