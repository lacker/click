# double free ends in a lifetime error

```c filename=heap_double_free.c
struct item {
    int32 value;
};

int32 heap_double_free() {
    struct item* item = malloc(sizeof(struct item));
    if (item == 0) {
        return -1;
    }
    item->value = 1;
    free(item);
    free(item);
    return 0;
}
```

```click
verifying "heap_double_free.c";

int32 heap_double_free() {
    ensures result == -1 or result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: cannot free an allocation whose lifetime has already ended
```
