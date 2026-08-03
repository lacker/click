struct borrowed_slice_buffer {
    int32 len;
    int32* data;
};

int32 borrowed_slice_buffer_get(
    struct borrowed_slice_buffer* owner,
    int32 data[],
    int32 length,
    int32 index
) {
    int32* backing;
    backing = owner->data;
    return backing[index];
}
