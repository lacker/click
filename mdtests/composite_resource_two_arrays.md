# composite resource bundles two arrays

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
    owns dst[0..1];
    views src[0..1];
}

verifying "copy_first.c";

int32 copy_first(int32 dst[], int32 src[]) {
    requires loadable(src[0..1]);
    consumes first_cell_copy_access(dst, src);

    produces first_cell_copy_access(dst, src) by {
        unfold(first_cell_copy_access(dst, src));
        symbolic_execute();
        fold(first_cell_copy_access(dst, src));
    }
}
```

```expect
pass
```
