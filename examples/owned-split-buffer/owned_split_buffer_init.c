struct owned_split_buffer {
    int32 split;
    int32 len;
    int32* data;
};

int32 owned_split_buffer_init(
    struct owned_split_buffer* owner,
    int32 data[],
    int32 length,
    int32 split
) {
    owner->split = split;
    owner->len = length;
    owner->data = data;
    return split;
}
