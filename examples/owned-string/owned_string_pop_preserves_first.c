struct owned_string {
    int32 len;
    int32 cap;
    int32* data;
};

int32 owned_string_pop_preserves_first(struct owned_string* owner) {
    int32 result;
    result = owned_string_pop(owner);
    return result;
}
