struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_len(struct owned_string* owner) {
    return owner->len;
}
