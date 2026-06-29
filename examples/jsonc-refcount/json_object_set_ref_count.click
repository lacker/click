verifying "json_object_set_ref_count.c";

int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
    requires valid_field(obj->ref_count);
    mutable_field(obj->ref_count) by frame;
    ensures returns_count: result == count by auto;
    ensures stores_count: obj->ref_count == count by auto;
}
