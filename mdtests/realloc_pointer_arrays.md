# realloc preserves pointer-array cells

Pointer-array `realloc` uses the eight-byte LP64 cell width and preserves
initialized pointer cells that fit in the new allocation. A successful result
has a fresh base and owns the complete resized range; a failed result leaves
the old allocation available to `free`.

```c filename=realloc_int32_pointer_array.c
int32 realloc_int32_pointer_array() {
    int32 value = 37;
    int32** slots = malloc(2 * sizeof(int32*));
    if (slots == 0) {
        return 0;
    }
    slots[0] = &value;
    int32** resized = realloc(slots, 3 * sizeof(int32*));
    if (resized == 0) {
        free(slots);
        return 0;
    }
    int32 result = *resized[0];
    free(resized);
    return result;
}
```

```c filename=realloc_uint8_pointer_array_shrink.c
uint8 realloc_uint8_pointer_array_shrink() {
    uint8 first = 42;
    uint8 second = 7;
    uint8** slots = malloc(2 * sizeof(uint8*));
    if (slots == 0) {
        return 0;
    }
    slots[0] = &first;
    slots[1] = &second;
    uint8** resized = realloc(slots, 1 * sizeof(uint8*));
    if (resized == 0) {
        free(slots);
        return 0;
    }
    uint8 result = *resized[0];
    free(resized);
    return result;
}
```

```click
verifying "realloc_int32_pointer_array.c";

int32 realloc_int32_pointer_array() {
    ensures result == 0 or result == 37 by auto;
}

verifying "realloc_uint8_pointer_array_shrink.c";

uint8 realloc_uint8_pointer_array_shrink() {
    ensures result == 0 or result == 42 by auto;
}
```

```expect
pass
```
