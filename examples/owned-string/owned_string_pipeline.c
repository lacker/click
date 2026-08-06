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
    int32 observed;
    ignored = owned_string_init(owner, data, capacity);
    ignored = owned_string_push(owner, first);
    observed = owned_string_get(owner, 0);
    ignored = owned_string_pop(owner);
    return observed;
}
