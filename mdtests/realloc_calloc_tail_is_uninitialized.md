# realloc leaves a grown calloc tail uninitialized

The bytes added by growing a zeroed allocation are not covered by the old
zero guarantee. Reading one of those bytes must remain an uninitialized read.

```c filename=realloc_calloc_tail_is_uninitialized.c
int32 realloc_calloc_tail_is_uninitialized() {
    int32* p = calloc(2, sizeof(int32));
    if (p == 0) {
        return -1;
    }
    int32* q = realloc(p, 3 * sizeof(int32));
    if (q == 0) {
        free(p);
        return -1;
    }
    return q[2];
}
```

```click
verifying "realloc_calloc_tail_is_uninitialized.c";

int32 realloc_calloc_tail_is_uninitialized() {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
