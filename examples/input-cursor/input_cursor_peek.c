struct input_cursor {
    int32 pos;
    int32 len;
    int32* data;
};

int32 input_cursor_peek(struct input_cursor* owner) {
    return owner->data[owner->pos];
}
