# realloc leaves a grown calloc uint8 tail uninitialized

The bytes added by growing a zeroed byte allocation are not covered by the
old zero guarantee. Reading a new tail byte must remain an uninitialized read.

```c filename=realloc_calloc_uint8_tail_is_uninitialized.c
uint8 realloc_calloc_uint8_tail_is_uninitialized() {
    uint8* p = calloc(2, sizeof(uint8));
    if (p == 0) {
        return 1;
    }
    uint8* q = realloc(p, 4 * sizeof(uint8));
    if (q == 0) {
        free(p);
        return 1;
    }
    return q[2];
}
```

```click
verifying "realloc_calloc_uint8_tail_is_uninitialized.c";

uint8 realloc_calloc_uint8_tail_is_uninitialized() {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
