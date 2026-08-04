# freed storage cannot be written

```c filename=heap_store_after_free.c
struct item {
    int32 value;
};

int32 heap_store_after_free() {
    struct item* item = malloc(sizeof(struct item));
    if (item == 0) {
        return -1;
    }
    item->value = 1;
    free(item);
    item->value = 2;
    return 0;
}
```

```click
verifying "heap_store_after_free.c";

int32 heap_store_after_free() {
    ensures result == -1 or result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: invalid memory access
```
