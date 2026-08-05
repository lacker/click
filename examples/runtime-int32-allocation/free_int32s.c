int32 free_int32s(int32 data[], int32 count) {
    free(data);
    return 0;
}
