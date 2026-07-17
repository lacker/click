struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_push_first(struct vector* owner, int32 value) {
    int32 index;
    int32* data;
    int32 result;
    index = owner->len;
    data = owner->data;
    data[index] = value;
    owner->len = index + 1;
    result = owner->len;
    return result;
}
