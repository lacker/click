struct input_cursor {
    int32 pos;
    int32 len;
    int32* data;
};

int32 input_cursor_init(
    struct input_cursor* owner,
    int32 data[],
    int32 length
) {
    owner->pos = 0;
    owner->len = length;
    owner->data = data;
    return 0;
}
