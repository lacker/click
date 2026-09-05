struct json_object {
    double value;
};

double json_object_scale_double(struct json_object* obj, int32 scale) {
    obj->value = obj->value * scale;
    return obj->value;
}
