# malloc supports pointer arrays

Heap allocation uses the ABI pointer width when the target is an `int32**` or
`uint8**`. The pointer-valued cells can then be initialized, loaded, and
reclaimed as one complete allocation.

```c filename=malloc_int32_pointer_array.c
int32 malloc_int32_pointer_array() {
    int32 value = 37;
    int32** slots = malloc(2 * sizeof(int32*));
    if (slots == 0) {
        return 0;
    }
    slots[0] = &value;
    int32 result = *slots[0];
    free(slots);
    return result;
}
```

```c filename=malloc_uint8_pointer_array.c
uint8 malloc_uint8_pointer_array() {
    uint8 value = 42;
    uint8** slots = malloc(2 * sizeof(uint8*));
    if (slots == 0) {
        return 0;
    }
    slots[0] = &value;
    uint8 result = *slots[0];
    free(slots);
    return result;
}
```

```click
verifying "malloc_int32_pointer_array.c";

int32 malloc_int32_pointer_array() {
    ensures result == 0 or result == 37 by auto;
}

verifying "malloc_uint8_pointer_array.c";

uint8 malloc_uint8_pointer_array() {
    ensures result == 0 or result == 42 by auto;
}
```

```expect
pass
```
