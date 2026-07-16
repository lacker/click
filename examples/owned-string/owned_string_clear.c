struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_clear(struct owned_string* owner) {
    owner->len = 0;
    owner->data[0] = 0;
    return 0;
}
