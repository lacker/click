struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_pipeline(
    struct vector* owner,
    int32 data[],
    int32 capacity,
    int32 first,
    int32 replacement
) {
    int32 observed;
    int32 ignored;
    observed = vector_init(owner, data, capacity);
    observed = vector_push_first(owner, first);
    observed = vector_get(owner, 0);
    observed = vector_set(owner, 0, replacement);
    observed = vector_get(owner, 0);
    ignored = vector_clear(owner);
    return observed;
}
