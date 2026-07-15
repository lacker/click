struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_get(struct vector* owner, int32 index) {
    int32* data;
    data = owner->data;
    return data[index];
}
