struct rc_object {
    int32 ref_count;
};

struct rc_object* rc_get(struct rc_object* obj) {
    obj->ref_count = obj->ref_count + 1;
    return obj;
}

int32 rc_put(struct rc_object* obj) {
    obj->ref_count = obj->ref_count - 1;
    if (obj->ref_count == 0) {
        return 1;
    } else {
        return 0;
    }
}

int32 rc_double_put_bad(struct rc_object* obj) {
    int32 first;
    first = rc_put(obj);
    return rc_put(obj);
}
