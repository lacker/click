struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 allocated_vector_push(struct vector* owner, int32 value) {
    int32 grown;
    int32 pushed_length;

    if (owner->len == owner->cap) {
        grown = vector_grow(owner);
        if (grown == 0) {
            return 0;
        }
    }
    pushed_length = vector_push(owner, value);
    return 1;
}
