struct ring_buffer {
    int32 head;
    int32 tail;
    int32* data;
};

int32 ring_buffer_push_wrap(
    struct ring_buffer* owner,
    int32 value
) {
    int32* data;
    data = owner->data;
    data[0] = value;
    owner->tail = 1;
    return data[0];
}
