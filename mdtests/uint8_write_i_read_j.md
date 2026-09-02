# uint8 write and read at distinct symbolic indices

This checks that a byte store at `buf[j]` does not invalidate a load at
`buf[k]` when the two byte-scaled indices are proven different.

```c filename=uint8_write_i_read_j.c
uint8 write_i_read_j(uint8 buf[], int32 j, int32 k, int32 n) {
    buf[j] = 9;
    return buf[k];
}
```

```click
verifying "uint8_write_i_read_j.c";

uint8 write_i_read_j(uint8 buf[], int32 j, int32 k, int32 n) {
    requires n >= 0 and n <= 2147483647;
    requires j >= 0 and j < n;
    requires k >= 0 and k < n;
    requires loadable(buf[0..n]);
    consumes buf[j..j + 1];
    views buf[k..k + 1];
    requires separate(memory(buf[j..j + 1]), memory(buf[k..k + 1]));
    mutable buf[j..j + 1] by auto;
    ensures keeps_k: result == old(buf[k]) by auto;
}
```

```expect
pass
```
