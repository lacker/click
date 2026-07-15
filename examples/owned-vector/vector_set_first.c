struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_set_first(struct vector* owner, int32 value) {
    int32* data;
    data = owner->data;
    data[0] = value;
    return data[0];
}
