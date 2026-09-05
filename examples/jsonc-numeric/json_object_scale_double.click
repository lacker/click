verifying "json_object_scale_double.c";

double json_object_scale_double(struct json_object* obj, int32 scale) {
    requires loadable(obj->value);
    requires isfinite(obj->value);
    requires isfinite(obj->value * scale);
    consumes obj->value;
    mutable obj->value;
    ensures returns_scaled: result == old(obj->value) * scale;
    ensures stores_scaled: obj->value == old(obj->value) * scale;
} by auto;
