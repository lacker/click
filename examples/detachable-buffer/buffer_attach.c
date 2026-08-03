struct detachable_buffer {
    int32 len;
    int32* data;
};

int32 detachable_buffer_attach(
    struct detachable_buffer* owner,
    int32 data[],
    int32 length
) {
    owner->len = length;
    owner->data = data;
    return owner->len;
}
