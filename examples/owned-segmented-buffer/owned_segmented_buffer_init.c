struct owned_segmented_buffer {
    int32 first_len;
    int32 second_len;
    int32* first_data;
    int32* second_data;
};

int32 owned_segmented_buffer_init(
    struct owned_segmented_buffer* owner,
    int32 first_data[],
    int32 first_len,
    int32 second_data[],
    int32 second_len
) {
    owner->first_len = first_len;
    owner->second_len = second_len;
    owner->first_data = first_data;
    owner->second_data = second_data;
    return first_len;
}
