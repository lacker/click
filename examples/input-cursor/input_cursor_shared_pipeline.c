struct input_cursor {
    int32 pos;
    int32 len;
    int32* data;
};

int32 input_cursor_shared_pipeline(
    struct input_cursor* left,
    struct input_cursor* right,
    int32 data[],
    int32 length
) {
    int32 ignored;
    int32 left_value;
    int32 right_value;
    ignored = input_cursor_init(left, data, length);
    ignored = input_cursor_init(right, data, length);
    left_value = input_cursor_take(left);
    right_value = input_cursor_peek(right);
    return right_value;
}
