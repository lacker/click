# calloc supports zeroed pointer arrays

Pointer-array `calloc` uses the same eight-byte cell width as pointer-array
`malloc`, but every successful pointer cell starts initialized to null. A cell
can then be overwritten with a real pointer before it is dereferenced, and the
complete allocation can be freed.

```c filename=calloc_int32_pointer_array.c
int32 calloc_int32_pointer_array() {
    int32 value = 37;
    int32** slots = calloc(2, sizeof(int32*));
    if (slots == 0) {
        return 0;
    }
    int32* initial = slots[0];
    if (initial != 0) {
        free(slots);
        return 0;
    }
    slots[1] = &value;
    int32 result = *slots[1];
    free(slots);
    return result;
}
```

```c filename=calloc_uint8_pointer_array.c
uint8 calloc_uint8_pointer_array() {
    uint8 value = 42;
    uint8** slots = calloc(2, sizeof(uint8*));
    if (slots == 0) {
        return 0;
    }
    uint8* initial = slots[0];
    if (initial != 0) {
        free(slots);
        return 0;
    }
    slots[1] = &value;
    uint8 result = *slots[1];
    free(slots);
    return result;
}
```

```click
verifying "calloc_int32_pointer_array.c";

int32 calloc_int32_pointer_array() {
    ensures result == 0 or result == 37 by auto;
}

verifying "calloc_uint8_pointer_array.c";

uint8 calloc_uint8_pointer_array() {
    ensures result == 0 or result == 42 by auto;
}
```

```expect
pass
```
