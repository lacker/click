# realloc preserves an initialized uint8 prefix

The modeled `realloc` builtin preserves initialized byte cells when a
`uint8*` allocation grows. A failed resize leaves the original byte buffer
available to free, while a successful resize transfers its ownership to the
fresh result.

```c filename=realloc_preserves_uint8_prefix.c
uint8 realloc_preserves_uint8_prefix(int32 count, int32 new_count) {
    uint8* p = malloc(count * sizeof(uint8));
    if (p == 0) {
        return 0;
    }
    p[0] = 42;
    uint8* q = realloc(p, new_count * sizeof(uint8));
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
verifying "realloc_preserves_uint8_prefix.c";

uint8 realloc_preserves_uint8_prefix(int32 count, int32 new_count) {
    requires 1 <= count;
    requires 1 <= new_count;
    ensures result == 0 or result == 42 by auto;
}
```

```expect
pass
```
