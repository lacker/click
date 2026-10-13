# A byte stored inside a calloc'd int32 is not zero under a symbolic index

The byte store at offset 5 lies inside the `int32` at index 1. A load at a
symbolic index `k` in `0..4` may be that element, so its value is not zero
whatever the facts say about `k == 1`: the load's address differs from the
byte's, but the four bytes it reads include it.

```c filename=calloc_byte_store_inside_symbolically_indexed_load_is_not_zero.c
int32 f(int32 k) {
    int32* p = calloc(4, sizeof(int32));
    if (p == 0) { return 0; }
    uint8* b = (uint8*)(void*) p;
    b[5] = 9;
    int32 r = p[k];
    free(p);
    return r;
}
```

```click
verifying "calloc_byte_store_inside_symbolically_indexed_load_is_not_zero.c";

int32 f(int32 k) {
    requires 0 <= k;
    requires k < 4;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: result == 0; left side evaluated to at(<state A>, *<pointer A>), right side evaluated to 0
```
