struct input_cursor {
    int32 pos;
    int32 len;
    int32* data;
};

int32 input_cursor_take(struct input_cursor* owner) {
    int32 value;
    value = owner->data[owner->pos];
    owner->pos = owner->pos + 1;
    return value;
}
