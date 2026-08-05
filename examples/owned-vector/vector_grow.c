struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_grow(struct vector* owner) {
    int32 old_capacity;
    int32 new_capacity;
    int32* old_data;
    int32* new_data;
    int32 copied;

    old_capacity = owner->cap;
    old_data = owner->data;
    new_capacity = old_capacity + 1;
    new_data = malloc(new_capacity * 4);
    if (new_data == 0) {
        return 0;
    }
    copied = vector_copy(
        new_data,
        old_data,
        owner->len,
        new_capacity,
        old_capacity
    );
    owner->data = new_data;
    owner->cap = new_capacity;
    free(old_data);
    return 1;
}
