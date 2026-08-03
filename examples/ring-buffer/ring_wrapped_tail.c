struct ring_buffer {
    int32 head;
    int32 tail;
    int32* data;
};

int32 ring_buffer_wrapped_tail(
    struct ring_buffer* owner
) {
    int32* data;
    data = owner->data;
    return data[0];
}
