struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_init(struct owned_string* owner, int32 data[], int32 capacity) {
    owner->len = 0;
    owner->cap = capacity;
    owner->data = data;
    data[0] = 0;
    return 0;
}
