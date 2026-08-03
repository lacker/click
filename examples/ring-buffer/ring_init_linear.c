struct ring_buffer {
    int32 head;
    int32 tail;
    int32* data;
};

int32 ring_buffer_init_linear(
    struct ring_buffer* owner,
    int32 data[],
    int32 head
) {
    owner->head = head;
    owner->tail = 4;
    owner->data = data;
    return owner->tail;
}
