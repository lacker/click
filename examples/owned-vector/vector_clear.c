struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_clear(struct vector* owner) {
    owner->len = 0;
    return owner->len;
}
