# write resources imply separate

This checks that two held owned-memory resources imply a `separate(...)` fact
for their ranges. No explicit `separate(...)` requirement is needed here.

```c filename=write_dst_read_src_from_write.c
int32 write_dst_read_src_from_write(int32* dst, int32* src) {
    dst[0] = 1;
    return src[0];
}
```

```click
verifying "write_dst_read_src_from_write.c";

int32 write_dst_read_src_from_write(int32* dst, int32* src) {
    consumes dst[0..1];
    consumes src[0..1];

    ensures src[0] == old(src[0]) by auto;
}
```

```expect
pass
```
