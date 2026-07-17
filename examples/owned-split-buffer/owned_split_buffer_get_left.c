struct owned_split_buffer {
    int32 split;
    int32 len;
    int32* data;
};

int32 owned_split_buffer_get_left(
    struct owned_split_buffer* owner,
    int32 index
) {
    return owner->data[index];
}
