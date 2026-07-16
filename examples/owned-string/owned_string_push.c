struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_push(struct owned_string* owner, int32 value) {
    int32 index;
    index = owner->len;
    owner->data[index] = value;
    owner->len = index + 1;
    owner->data[index + 1] = 0;
    return owner->len;
}
