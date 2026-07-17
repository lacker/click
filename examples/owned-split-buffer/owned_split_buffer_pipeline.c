struct owned_split_buffer {
    int32 split;
    int32 len;
    int32* data;
};

int32 owned_split_buffer_pipeline(
    struct owned_split_buffer* owner,
    int32 data[],
    int32 length,
    int32 left_value,
    int32 right_value
) {
    int32 ignored;
    int32 result;
    ignored = owned_split_buffer_init(owner, data, length, 1);
    ignored = owned_split_buffer_set_left(owner, 0, left_value);
    ignored = owned_split_buffer_set_right(owner, 1, right_value);
    ignored = owned_split_buffer_move_right(owner);
    result = owned_split_buffer_get_left(owner, 1);
    return result;
}
