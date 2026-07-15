struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_set(struct vector* owner, int32 index, int32 value) {
    int32* data;
    data = owner->data;
    data[index] = value;
    return data[index];
}
