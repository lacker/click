struct owned_segmented_buffer {
    int32 first_len;
    int32 second_len;
    int32* first_data;
    int32* second_data;
};

int32 owned_segmented_buffer_pipeline(
    struct owned_segmented_buffer* owner,
    int32 first_data[],
    int32 first_len,
    int32 second_data[],
    int32 second_len,
    int32 first_value,
    int32 second_value
) {
    int32 ignored;
    int32 result;
    ignored = owned_segmented_buffer_init(
        owner,
        first_data,
        first_len,
        second_data,
        second_len
    );
    ignored = owned_segmented_buffer_set_first(owner, 0, first_value);
    ignored = owned_segmented_buffer_set_second(owner, 0, second_value);
    result = owned_segmented_buffer_get_first(owner, 0);
    return result;
}
