# realloc preserves complete cells in arbitrary byte layouts

Heap allocation and `realloc` use byte extents even when the receiving pointer
has a wider logical element type. Typed loads and stores remain bounded by the
actual byte extent, and initialized cells are copied only when the complete
cell fits in the resized block.

```c filename=arbitrary_layout_realloc.c
struct item {
    int32 value;
    int32 tail;
};

int32 arbitrary_int32_realloc() {
    int32* data = malloc(5);
    if (data == 0) {
        return 0;
    }
    data[0] = 7;
    int32* resized = realloc(data, 9);
    if (resized == 0) {
        free(data);
        return 0;
    }
    data = resized;
    int32 result = data[0];
    free(data);
    return result;
}

int32 arbitrary_struct_realloc() {
    struct item* item = malloc(6);
    if (item == 0) {
        return 0;
    }
    item->value = 11;
    struct item* resized = realloc(item, 10);
    if (resized == 0) {
        free(item);
        return 0;
    }
    item = resized;
    int32 result = item->value;
    free(item);
    return result;
}
```

```click
verifying "arbitrary_layout_realloc.c";

int32 arbitrary_int32_realloc() {
    ensures result == 0 or result == 7 by auto;
}

int32 arbitrary_struct_realloc() {
    ensures result == 0 or result == 11 by auto;
}
```

```expect
pass
```
