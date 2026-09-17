# realloc preserves the zeroed calloc uint8 prefix

When a zeroed byte allocation grows, `realloc` keeps the preserved prefix
zeroed and transfers the complete byte-buffer resources to the new pointer.

```c filename=realloc_preserves_calloc_uint8_prefix.c
uint8 realloc_preserves_calloc_uint8_prefix() {
    uint8* p = calloc(2, sizeof(uint8));
    if (p == 0) {
        return 1;
    }
    uint8* q = realloc(p, 4 * sizeof(uint8));
    if (q == 0) {
        free(p);
        return 1;
    }
    uint8 result = q[1];
    free(q);
    return result;
}
```

```click
verifying "realloc_preserves_calloc_uint8_prefix.c";

uint8 realloc_preserves_calloc_uint8_prefix() {
    ensures result == 0 or result == 1 by auto;
}
```

```expect
pass
```
