struct ring_buffer {
    int32 head;
    int32 tail;
    int32* data;
};

int32 ring_buffer_pipeline(
    struct ring_buffer* owner,
    int32 replacement
) {
    int32 ignored;
    int32 pushed;
    pushed = ring_buffer_push_wrap(owner, replacement);
    ignored = ring_buffer_pop_to_linear(owner);
    return pushed;
}
