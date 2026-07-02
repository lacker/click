# represented resource disjoint fact

This checks that a represented resource can package a `disjoint(...)` fact and
that opening the resource exposes that fact to effect reasoning.

```c filename=clobber_dst_packaged.c
int32 clobber_dst_packaged(int32* dst, int32* src) {
    dst[0] = 1;
    return src[0];
}
```

```click
affine resource separated_first_cells(dst: int32*, src: int32*) {
    contains write(dst[0..1]);
    contains read(src[0..1]);
    fact disjoint(dst[0..1], src[0..1]);
}

verifying "clobber_dst_packaged.c";

int32 clobber_dst_packaged(int32* dst, int32* src) {
    requires valid_range(dst[0..1]);
    requires valid_range(src[0..1]);
    requires separated_first_cells(dst, src);

    ensures separated_first_cells(dst, src) by {
        open(separated_first_cells(dst, src));
        symbolic_execute();
        close(separated_first_cells(dst, src));
    }

    ensures source_unchanged: src[0] == old(src[0]) by {
        open(separated_first_cells(dst, src));
        symbolic_execute();
        close(separated_first_cells(dst, src));
    }
}
```

```expect
pass
```
