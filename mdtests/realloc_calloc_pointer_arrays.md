# realloc preserves zeroed pointer-array prefixes

When a zeroed pointer array grows, the retained prefix continues to contain
initialized null pointers. The new tail is writable but has no inherited zero
guarantee.

```c filename=realloc_calloc_int32_pointer_array.c
int32 realloc_calloc_int32_pointer_array() {
    int32 value = 37;
    int32** slots = calloc(2, sizeof(int32*));
    if (slots == 0) {
        return 1;
    }
    int32** resized = realloc(slots, 3 * sizeof(int32*));
    if (resized == 0) {
        free(slots);
        return 1;
    }
    int32* retained = resized[1];
    if (retained != 0) {
        free(resized);
        return 1;
    }
    resized[2] = &value;
    int32 result = *resized[2];
    free(resized);
    return result;
}
```

```c filename=realloc_calloc_uint8_pointer_array.c
uint8 realloc_calloc_uint8_pointer_array() {
    uint8 value = 42;
    uint8** slots = calloc(2, sizeof(uint8*));
    if (slots == 0) {
        return 1;
    }
    uint8** resized = realloc(slots, 3 * sizeof(uint8*));
    if (resized == 0) {
        free(slots);
        return 1;
    }
    uint8* retained = resized[1];
    if (retained != 0) {
        free(resized);
        return 1;
    }
    resized[2] = &value;
    uint8 result = *resized[2];
    free(resized);
    return result;
}
```

```click
verifying "realloc_calloc_int32_pointer_array.c";

int32 realloc_calloc_int32_pointer_array() {
    ensures result == 1 or result == 37 by auto;
}

verifying "realloc_calloc_uint8_pointer_array.c";

uint8 realloc_calloc_uint8_pointer_array() {
    ensures result == 1 or result == 42 by auto;
}
```

```expect
pass
```
