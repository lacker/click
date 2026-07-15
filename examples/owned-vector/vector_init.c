struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_init(struct vector* owner, int32 data[], int32 capacity) {
    owner->len = 0;
    owner->cap = capacity;
    owner->data = data;
    return owner->len;
}
