# represented resource bundles two arrays

This checks the simplest compositional resource shape: one abstract token
bundles write permission for one array and read permission for another.

```c filename=copy_first.c
int32 copy_first(int32 dst[], int32 src[]) {
    dst[0] = src[0];
    return dst[0];
}
```

```click
resource first_cell_copy_access(dst: int32*, src: int32*) {
    contains write(dst[0..1]);
    contains read(src[0..1]);
}

verifying "copy_first.c";

int32 copy_first(int32 dst[], int32 src[]) {
    requires valid_range(src[0..1]);
    requires first_cell_copy_access(dst, src);

    ensures first_cell_copy_access(dst, src) by {
        unpack(first_cell_copy_access(dst, src));
        symbolic_execute();
        pack(first_cell_copy_access(dst, src));
    }
}
```

```expect
pass
```
