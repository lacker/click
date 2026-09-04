# realloc retains byte bounds for typed accesses

An arbitrary byte-layout allocation may be viewed through a typed pointer, but
an access must still fit completely within the byte extent after `realloc`.

```c filename=arbitrary_layout_realloc_bounds.c
int32 arbitrary_layout_realloc_bounds() {
    int32* data = malloc(5);
    if (data == 0) {
        return 0;
    }
    int32* resized = realloc(data, 6);
    if (resized == 0) {
        free(data);
        return 0;
    }
    data = resized;
    data[1] = 13;
    free(data);
    return 0;
}
```

```click
verifying "arbitrary_layout_realloc_bounds.c";

int32 arbitrary_layout_realloc_bounds() {
    ensures result == 0 by auto;
}
```

```expect
fail: missing resource fact
```
