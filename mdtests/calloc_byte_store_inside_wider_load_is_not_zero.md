# A byte stored inside a calloc'd int32 makes that int32 nonzero

`calloc` memory reads as zero until overwritten. The byte store at offset 5
overwrites one byte of the `int32` at offset 4, so that cell no longer reads
as zero: its value is `9 << 8`, which is `2304`.

```c filename=calloc_byte_store_inside_wider_load_is_not_zero.c
int32 f() {
    int32* p = calloc(4, sizeof(int32));
    if (p == 0) { return 0; }
    uint8* b = (uint8*)(void*) p;
    b[5] = 9;
    int32 r = p[1];
    free(p);
    return r;
}
```

```click
verifying "calloc_byte_store_inside_wider_load_is_not_zero.c";

int32 f() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: result == 0; left side evaluated to at(statement(9).exit, r), right side evaluated to 0
```
