# uint8 fill loop retains byte-range reasoning

This keeps the C byte-buffer fill loop unchanged while checking that every
indexed store uses byte-scaled pointer arithmetic and that the postcondition
can still name the complete byte range.

```c filename=uint8_fill_loop_range.c
int32 fill_bytes(uint8 buf[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        buf[i] = 0;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "uint8_fill_loop_range.c";

int32 fill_bytes(uint8 buf[], int32 n) {
    requires n >= 0 and n <= 2147483647;
    requires loadable(buf[0..n]);
    consumes buf[0..n];
    ensures filled_length: result == n;
    ensures byte_range_remains_loadable: loadable(buf[0..n]);
} by {
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
