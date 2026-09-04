# heap struct arrays retain element bounds

An indexed heap struct array may access only elements within the allocated
struct-sized extent. The verifier must reject an out-of-bounds member access.

```c filename=heap_struct_array_bounds.c
struct item {
    int32 value;
};

int32 heap_struct_array_bounds() {
    struct item* items = malloc(2 * sizeof(struct item));
    if (items == 0) {
        return 0;
    }
    items[2].value = 1;
    free(items);
    return 0;
}
```

```click
verifying "heap_struct_array_bounds.c";

int32 heap_struct_array_bounds() {
    ensures result == 0 by auto;
}
```

```expect
fail: missing resource fact
```
