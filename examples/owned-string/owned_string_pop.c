struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_pop(struct owned_string* owner) {
    int32 index;
    int32 value;
    index = owner->len - 1;
    value = owner->data[index];
    owner->data[index] = 0;
    owner->len = index;
    return value;
}
