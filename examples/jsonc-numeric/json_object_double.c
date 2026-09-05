struct json_object {
    double value;
};

double json_object_get_double(struct json_object* obj) {
    return obj->value;
}
