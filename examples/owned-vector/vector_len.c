struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_len(struct vector* owner) {
    return owner->len;
}
