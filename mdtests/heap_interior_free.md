# free requires the allocation base

```c filename=heap_interior_free.c
struct item {
    int32 first;
    int32 second;
};

int32 heap_interior_free() {
    struct item* item = malloc(sizeof(struct item));
    if (item == 0) {
        return -1;
    }
    item->first = 1;
    item->second = 2;
    free(item + 1);
    return 0;
}
```

```click
verifying "heap_interior_free.c";

int32 heap_interior_free() {
    ensures result == -1 or result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: cannot free an interior pointer; free requires the allocation base
```
