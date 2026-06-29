struct json_object {
    int32 ref_count;
};

int32 json_object_inc_ref_count(struct json_object* obj) {
    obj->ref_count = obj->ref_count + 1;
    return obj->ref_count;
}
