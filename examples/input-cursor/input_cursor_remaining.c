struct input_cursor {
    int32 pos;
    int32 len;
    int32* data;
};

int32 input_cursor_remaining(struct input_cursor* owner) {
    return owner->len - owner->pos;
}
