# freed storage cannot be read

```c filename=heap_use_after_free.c
struct item {
    int32 value;
};

int32 heap_use_after_free() {
    struct item* item = malloc(sizeof(struct item));
    if (item == 0) {
        return -1;
    }
    item->value = 1;
    free(item);
    return item->value;
}
```

```click
verifying "heap_use_after_free.c";

int32 heap_use_after_free() {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: invalid memory access
```
