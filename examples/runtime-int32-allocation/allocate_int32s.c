int32* allocate_int32s(int32 count) {
    int32* data;
    data = malloc(count * 4);
    return data;
}
