struct owned_split_buffer {
    int32 split;
    int32 len;
    int32* data;
};

int32 owned_split_buffer_set_right(
    struct owned_split_buffer* owner,
    int32 index,
    int32 value
) {
    owner->data[index] = value;
    return value;
}
