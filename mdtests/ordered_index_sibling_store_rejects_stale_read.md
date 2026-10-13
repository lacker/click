# A common upper bound does not separate sibling indices

```c filename=ordered_index_sibling_store_rejects_stale_read.c
int32 f(int32* data, int32 len, int32 x, int32 y, int32 z) {
    data[x] = 100;
    data[y] = 1;
    return data[x];
}
```

```click
verifying "ordered_index_sibling_store_rejects_stale_read.c";
int32 f(int32* data, int32 len, int32 x, int32 y, int32 z) {
    owns data[0..len];
    requires 0 <= x;
    requires 0 <= y;
    requires x < z;
    requires y < z;
    requires z < len;
    ensures result == 100;
} by { step(); step(); step(); simp(); }
```

```expect
fail: unclosed goal
```
