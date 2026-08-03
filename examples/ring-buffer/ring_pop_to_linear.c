struct ring_buffer {
    int32 head;
    int32 tail;
    int32* data;
};

int32 ring_buffer_pop_to_linear(
    struct ring_buffer* owner
) {
    int32 result;
    int32* data;
    data = owner->data;
    result = data[0];
    owner->tail = 4;
    return result;
}
