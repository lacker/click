# realloc leaves a grown calloc pointer-array tail uninitialized

The zero guarantee from a pointer-array `calloc` applies only to the retained
prefix. Loading a new pointer cell after growth is an uninitialized read.

```c filename=realloc_calloc_pointer_array_tail_is_uninitialized.c
int32* realloc_calloc_pointer_array_tail_is_uninitialized() {
    int32** slots = calloc(1, sizeof(int32*));
    if (slots == 0) {
        return 0;
    }
    int32** resized = realloc(slots, 2 * sizeof(int32*));
    if (resized == 0) {
        free(slots);
        return 0;
    }
    return resized[1];
}
```

```click
verifying "realloc_calloc_pointer_array_tail_is_uninitialized.c";

int32* realloc_calloc_pointer_array_tail_is_uninitialized() {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
