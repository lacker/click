# heap arrays of structs use ABI stride

Heap allocation accepts a runtime count multiplied by `sizeof(struct T)` when
the target is `struct T*`. Indexed member access uses the complete ABI layout
size for each element, while `calloc` and `realloc` retain their existing
zeroing and prefix-preservation guarantees.

```c filename=malloc_struct_array.c
struct item {
    uint8 tag;
    int32 value;
    struct item* next;
};

int32 malloc_struct_array() {
    struct item* items = malloc(2 * sizeof(struct item));
    if (items == 0) {
        return 0;
    }
    items[0].tag = 3;
    items[1].value = 7;
    int32 result = items[0].tag + items[1].value;
    free(items);
    return result;
}
```

```c filename=calloc_struct_array.c
struct item {
    uint8 tag;
    int32 value;
    struct item* next;
};

int32 calloc_struct_array() {
    struct item* items = calloc(2, sizeof(struct item));
    if (items == 0) {
        return 1;
    }
    int32 result = items[0].tag + items[1].value + (items[0].next != 0);
    free(items);
    return result;
}
```

```c filename=realloc_struct_array.c
struct item {
    uint8 tag;
    int32 value;
    struct item* next;
};

int32 realloc_struct_array() {
    struct item* items = calloc(2, sizeof(struct item));
    if (items == 0) {
        return 0;
    }
    items[0].value = 7;
    items[1].value = 11;
    struct item* resized = realloc(items, 3 * sizeof(struct item));
    if (resized == 0) {
        free(items);
        return 0;
    }
    items = resized;
    int32 result = items[0].value + items[1].value;
    free(items);
    return result;
}
```

```c filename=malloc_byte_struct_array.c
struct tiny {
    uint8 first;
    uint8 second;
};

int32 malloc_byte_struct_array() {
    struct tiny* items = malloc(3 * sizeof(struct tiny));
    if (items == 0) {
        return 0;
    }
    items[0].second = 4;
    items[2].first = 5;
    int32 result = items[0].second + items[2].first;
    free(items);
    return result;
}
```

```c filename=struct_pointer_stride.c
struct tiny {
    uint8 first;
    uint8 second;
};

int32 struct_pointer_stride() {
    struct tiny* items = malloc(2 * sizeof(struct tiny));
    if (items == 0) {
        return 0;
    }
    items[1].first = 6;
    struct tiny* second = items + 1;
    int32 result = second->first;
    free(items);
    return result;
}
```

```click
verifying "malloc_struct_array.c";

int32 malloc_struct_array() {
    ensures result == 0 or result == 10 by auto;
}

verifying "calloc_struct_array.c";

int32 calloc_struct_array() {
    ensures result == 0 or result == 1 by auto;
}

verifying "realloc_struct_array.c";

int32 realloc_struct_array() {
    ensures result == 0 or result == 18 by auto;
}

verifying "malloc_byte_struct_array.c";

int32 malloc_byte_struct_array() {
    ensures result == 0 or result == 9 by auto;
}

verifying "struct_pointer_stride.c";

int32 struct_pointer_stride() {
    ensures result == 0 or result == 6 by auto;
}
```

```expect
pass
```
