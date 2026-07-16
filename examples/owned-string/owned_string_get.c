struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_get(struct owned_string* owner, int32 index) {
    return owner->data[index];
}
