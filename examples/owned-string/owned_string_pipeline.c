struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_pipeline(
    struct owned_string* owner,
    int32 data[],
    int32 capacity,
    int32 first
) {
    int32 ignored;
    ignored = owned_string_init(owner, data, capacity);
    ignored = owned_string_clear(owner);
    return first;
}
