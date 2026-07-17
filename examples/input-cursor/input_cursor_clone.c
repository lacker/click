struct input_cursor {
    int32 pos;
    int32 len;
    int32* data;
};

int32 input_cursor_clone(
    struct input_cursor* target,
    struct input_cursor* source
) {
    target->pos = source->pos;
    target->len = source->len;
    target->data = source->data;
    return target->pos;
}
