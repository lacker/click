struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_set(
    struct owned_string* owner,
    int32 index,
    int32 value
) {
    owner->data[index] = value;
    return value;
}
