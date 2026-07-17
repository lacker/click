struct owned_split_buffer {
    int32 split;
    int32 len;
    int32* data;
};

int32 owned_split_buffer_move_right(struct owned_split_buffer* owner) {
    owner->split = owner->split + 1;
    return owner->split;
}
