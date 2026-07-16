struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_push_preserves_first(
    struct owned_string* owner,
    int32 data[],
    int32 value
) {
    int32 result;
    result = owned_string_push(owner, value);
    return result;
}
