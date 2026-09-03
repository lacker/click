# realloc preserves the fitting prefix when shrinking uint8 storage

Shrinking a byte buffer discards only cells outside the new extent. The
initialized bytes that fit remain readable after the successful resize.

```c filename=realloc_shrinks_uint8_prefix.c
uint8 realloc_shrinks_uint8_prefix() {
    uint8* p = malloc(3 * sizeof(uint8));
    if (p == 0) {
        return 0;
    }
    p[0] = 42;
    p[1] = 7;
    uint8* q = realloc(p, 1 * sizeof(uint8));
    if (q == 0) {
        free(p);
        return 0;
    }
    uint8 result = q[0];
    free(q);
    return result;
}
```

```click
verifying "realloc_shrinks_uint8_prefix.c";

uint8 realloc_shrinks_uint8_prefix() {
    ensures result == 0 or result == 42 by auto;
}
```

```expect
pass
```
