# realloc preserves the zeroed calloc prefix

When a zeroed `calloc` allocation grows, `realloc` keeps the old bytes zero
and gives the new tail its ordinary uninitialized allocation semantics.

```c filename=realloc_preserves_calloc_prefix.c
int32 realloc_preserves_calloc_prefix() {
    int32* p = calloc(2, sizeof(int32));
    if (p == 0) {
        return -1;
    }
    int32* q = realloc(p, 3 * sizeof(int32));
    if (q == 0) {
        free(p);
        return -1;
    }
    int32 result = q[1];
    free(q);
    return result;
}
```

```click
verifying "realloc_preserves_calloc_prefix.c";

int32 realloc_preserves_calloc_prefix() {
    ensures result == 0 or result == -1 by auto;
}
```

```expect
pass
```
