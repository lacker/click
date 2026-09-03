# pointer-array allocation has element bounds

An allocation of one pointer cell has one valid pointer-array element. Writing
the one-past cell must fail rather than being silently accepted because the
allocation is byte-sized.

```c filename=malloc_pointer_array_bounds.c
int32 malloc_pointer_array_bounds() {
    int32** slots = malloc(sizeof(int32*));
    if (slots == 0) {
        return 0;
    }
    slots[1] = 0;
    return 0;
}
```

```click
verifying "malloc_pointer_array_bounds.c";

int32 malloc_pointer_array_bounds() {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact
```
