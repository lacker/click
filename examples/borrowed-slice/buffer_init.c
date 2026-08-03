struct borrowed_slice_buffer {
    int32 len;
    int32* data;
};

int32 borrowed_slice_buffer_init(
    struct borrowed_slice_buffer* owner,
    int32 data[],
    int32 length
) {
    owner->len = length;
    owner->data = data;
    return owner->len;
}
