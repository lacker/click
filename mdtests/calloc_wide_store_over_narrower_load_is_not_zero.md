# An int64 stored over a calloc'd int32 makes that int32 nonzero

The mirror of
`mdtests/calloc_byte_store_inside_wider_load_is_not_zero.md`: the eight-byte
store at offset 0 covers the `int32` at offset 4, whose value is then
`(1 << 40) >> 32`, which is `256`.

```c filename=calloc_wide_store_over_narrower_load_is_not_zero.c
int32 f() {
    int32* p = calloc(4, sizeof(int32));
    if (p == 0) { return 0; }
    int64* w = (int64*)(void*) p;
    w[0] = 1099511627776;
    int32 r = p[1];
    free(p);
    return r;
}
```

```click
verifying "calloc_wide_store_over_narrower_load_is_not_zero.c";

int32 f() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: result == 0; left side evaluated to at(<state A>, *<pointer A>), right side evaluated to 0
```
