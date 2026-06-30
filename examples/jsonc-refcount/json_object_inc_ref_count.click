verifying "json_object_inc_ref_count.c";

int32 json_object_inc_ref_count(struct json_object* obj) {
    requires valid_field(obj->ref_count);
    requires write(obj[0..1]);
    requires obj->ref_count < 2147483647;
    mutable_field(obj->ref_count) by frame;
    ensures returns_incremented: result == old(obj->ref_count) + 1 by auto;
    ensures stores_incremented: obj->ref_count == old(obj->ref_count) + 1 by auto;
}
