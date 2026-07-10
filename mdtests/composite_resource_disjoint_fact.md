# composite resource disjoint fact

This checks that a composite resource can package a `disjoint(...)` fact and
that unfolding the resource exposes that fact to effect reasoning.

```c filename=clobber_dst_packaged.c
int32 clobber_dst_packaged(int32* dst, int32* src) {
    dst[0] = 1;
    return src[0];
}
```

```click
resource separated_first_cells(dst: int32*, src: int32*) {
    contains write(dst[0..1]);
    contains read(src[0..1]);
    fact disjoint(dst[0..1], src[0..1]);
}

verifying "clobber_dst_packaged.c";

int32 clobber_dst_packaged(int32* dst, int32* src) {
    requires loadable(dst[0..1]);
    requires loadable(src[0..1]);
    requires separated_first_cells(dst, src);

    ensures separated_first_cells(dst, src) by {
        unfold(separated_first_cells(dst, src));
        symbolic_execute();
        fold(separated_first_cells(dst, src));
    }

    ensures source_unchanged: src[0] == old(src[0]) by {
        unfold(separated_first_cells(dst, src));
        symbolic_execute();
        fold(separated_first_cells(dst, src));
    }
}
```

```expect
pass
```
