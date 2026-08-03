struct borrowed_slice_buffer {
    int32 len;
    int32* data;
};

int32 borrowed_slice_buffer_pipeline(
    struct borrowed_slice_buffer* owner,
    int32 data[],
    int32 length,
    int32 start,
    int32 end,
    int32 replacement
) {
    int32 ignored;
    int32 observed;
    ignored = borrowed_slice_buffer_init(owner, data, length);
    ignored = borrowed_slice_buffer_borrow(owner, data, length, start, end);
    observed = borrowed_slice_set(data, start, end, start, replacement);
    ignored = borrowed_slice_buffer_return(owner, data, length, start, end);
    ignored = borrowed_slice_buffer_get(owner, data, length, start);
    return observed;
}
