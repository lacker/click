verifying "json_object_set_ref_count.c";

int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
    requires loadable(obj->ref_count);
    consumes obj[0..1];
    mutable_field(obj->ref_count) by frame;
    ensures returns_count: result == count by auto;
    ensures stores_count: obj->ref_count == count by auto;
}
