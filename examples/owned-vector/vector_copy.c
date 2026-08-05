int32 vector_copy(
    int32 dst[],
    int32 src[],
    int32 length,
    int32 dst_capacity,
    int32 src_capacity
) {
    int32 i;
    i = 0;
    while (i < length) {
        dst[i] = src[i];
        i = i + 1;
    }
    return i;
}
