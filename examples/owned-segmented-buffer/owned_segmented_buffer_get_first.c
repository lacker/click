struct owned_segmented_buffer {
    int32 first_len;
    int32 second_len;
    int32* first_data;
    int32* second_data;
};

int32 owned_segmented_buffer_get_first(
    struct owned_segmented_buffer* owner,
    int32 index
) {
    return owner->first_data[index];
}
