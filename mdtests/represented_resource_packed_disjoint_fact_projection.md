# represented resource packed disjoint fact projection

This checks that a packed represented resource can expose a packaged
`disjoint(...)` fact to effect reasoning without exposing any contained
permissions.

```c filename=write_dst_read_src.c
int32 write_dst_read_src(int32* dst, int32* src) {
    dst[0] = 1;
    return src[0];
}
```

```click
affine resource separated_first_cells(dst: int32*, src: int32*) {
    fact disjoint(dst[0..1], src[0..1]);
}

verifying "write_dst_read_src.c";

int32 write_dst_read_src(int32* dst, int32* src) {
    requires write(dst[0..1]);
    requires read(src[0..1]);
    requires separated_first_cells(dst, src);

    ensures src[0] == old(src[0]) by auto;
    ensures separated_first_cells(dst, src) by auto;
}
```

```expect
pass
```
