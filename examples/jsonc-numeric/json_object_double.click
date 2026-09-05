verifying "json_object_double.c";

double json_object_get_double(struct json_object* obj) {
    requires loadable(obj->value);
    requires isfinite(obj->value);
    views obj->value;
    ensures returns_value: result == obj->value;
    immutable;
} by auto;
