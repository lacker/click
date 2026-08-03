struct detachable_buffer {
    int32 len;
    int32* data;
};

int32 detachable_buffer_pipeline(
    struct detachable_buffer* owner,
    int32 data[],
    int32 length,
    int32 replacement
) {
    int32 ignored;
    int32 observed;
    ignored = detachable_buffer_init(owner, data, length);
    ignored = detachable_buffer_detach(owner, data, length);
    observed = detachable_buffer_set_first(data, length, replacement);
    ignored = detachable_buffer_attach(owner, data, length);
    ignored = detachable_buffer_get(owner, 0);
    return observed;
}
