verifying "json_object_ref_count.c";

int32 json_object_get_ref_count(struct json_object* obj) {
    requires loadable(obj->ref_count);
    requires read(obj[0..1]);
    ensures returns_ref_count: result == obj->ref_count by auto;
    immutable by frame;
}
