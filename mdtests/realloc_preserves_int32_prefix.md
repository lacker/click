# realloc preserves initialized prefix and transfers ownership

The modeled `realloc` builtin preserves initialized cells that fit in the new
`int32` allocation. A failed resize leaves the original allocation available
to free; a successful resize returns a fresh allocation and retires the old
one.

```c filename=realloc_preserves_int32_prefix.c
int32 realloc_preserves_int32_prefix() {
    int32* p = malloc(2 * sizeof(int32));
    if (p == 0) {
        return 0;
    }
    p[0] = 7;
    int32* q = realloc(p, 3 * sizeof(int32));
    if (q == 0) {
        free(p);
        return 0;
    }
    p = q;
    int32 result = p[0];
    free(p);
    return result;
}
```

```click
verifying "realloc_preserves_int32_prefix.c";

int32 realloc_preserves_int32_prefix() {
    ensures result == 0 or result == 7 by auto;
}
```

```expect
pass
```
