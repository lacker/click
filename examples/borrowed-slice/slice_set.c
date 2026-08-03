int32 borrowed_slice_set(
    int32 data[],
    int32 start,
    int32 end,
    int32 index,
    int32 value
) {
    data[index] = value;
    return data[index];
}
