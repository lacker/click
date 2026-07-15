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
    int32* current;
    int32 observed;
    observed = vector_init(owner, data, capacity);
    current = owner->data;
    current[0] = first;
    owner->len = 1;
    observed = vector_get(owner, 0);
    current[0] = replacement;
    observed = vector_get(owner, 0);
    owner->len = 0;
    return observed;
}
