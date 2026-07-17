struct owned_segmented_buffer {
    int32 first_len;
    int32 second_len;
    int32* first_data;
    int32* second_data;
};

int32 owned_segmented_buffer_swap(struct owned_segmented_buffer* owner) {
    int32 saved_len;
    int32* saved_data;
    saved_len = owner->first_len;
    saved_data = owner->first_data;
    owner->first_len = owner->second_len;
    owner->first_data = owner->second_data;
    owner->second_len = saved_len;
    owner->second_data = saved_data;
    return owner->first_len;
}
