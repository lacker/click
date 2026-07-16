struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_fill(struct vector* owner, int32 value) {
    int32 i;
    i = 0;
    while (i < owner->len) {
        owner->data[i] = value;
        i = i + 1;
    }
    return owner->len;
}
