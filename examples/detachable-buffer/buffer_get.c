struct detachable_buffer {
    int32 len;
    int32* data;
};

int32 detachable_buffer_get(struct detachable_buffer* owner, int32 index) {
    int32* data;
    data = owner->data;
    return data[index];
}
