struct vector {
    int32 len;
    int32 cap;
    int32* data;
};

int32 vector_replace_if(
    struct vector* owner,
    int32 index,
    int32 replacement,
    int32 replace
) {
    int32 original;
    int32 selected;
    original = vector_get(owner, index);
    if (replace != 0) {
        selected = vector_set(owner, index, replacement);
    } else {
        selected = vector_set(owner, index, original);
    }
    return selected;
}
