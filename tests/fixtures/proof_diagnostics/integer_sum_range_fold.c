int32 sum(int32 a[], int32 n) {
    int32 total;
    int32 i;
    total = 0;
    i = 0;
    while (i < n) {
        total = total + a[i];
        i = i + 1;
    }
    return total;
}
