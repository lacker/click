verifying "json_object_set_ref_count.c";

int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
    requires loadable(obj->ref_count);
    consumes obj[0..1];
    mutable obj->ref_count;
    ensures returns_count: result == count;
    ensures stores_count: obj->ref_count == count;
} by auto;
