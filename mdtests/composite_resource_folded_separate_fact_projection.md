# composite resource folded separate fact projection

This checks that a folded composite resource can expose a packaged
`separate(...)` fact to effect reasoning without exposing any contained
permissions.

```c filename=write_dst_read_src.c
int32 write_dst_read_src(int32* dst, int32* src) {
    dst[0] = 1;
    return src[0];
}
```

```click
resource separated_first_cells(dst: int32*, src: int32*) {
    fact separate(memory(dst[0..1]), memory(src[0..1]));
}

verifying "write_dst_read_src.c";

int32 write_dst_read_src(int32* dst, int32* src) {
    consumes dst[0..1];
    views src[0..1];
    consumes separated_first_cells(dst, src);

    ensures src[0] == old(src[0]) by auto;
    produces separated_first_cells(dst, src) by auto;
}
```

```expect
pass
```
