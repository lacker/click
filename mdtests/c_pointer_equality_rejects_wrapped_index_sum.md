# a wrapped index sum does not make two pointers equal

`data + i + j` with `i == INT_MAX` and `j == 1` and `data + k` with
`k == INT_MIN` have equal 32-bit index sums but exact offsets of `+2^33` and
`-2^33` bytes, so `p == q` must not be decided true. Forming `data + INT_MAX
+ 1` is also undefined behavior in C.

```c filename=c_pointer_equality_rejects_wrapped_index_sum.c
int32 ptr_cmp(int32 data[], int32 i, int32 j, int32 k) {
    int32* p;
    int32* q;
    p = data + i + j;
    q = data + k;
    if (p == q) {
        return 1;
    }
    return 0;
}
```

```click
verifying "c_pointer_equality_rejects_wrapped_index_sum.c";

int32 ptr_cmp(int32 data[], int32 i, int32 j, int32 k) {
    requires i == 2147483647;
    requires j == 1;
    requires k == -2147483647 - 1;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: pointer arithmetic left the pointed-to object
```
