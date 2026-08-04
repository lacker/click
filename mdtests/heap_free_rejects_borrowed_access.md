# borrowed access cannot free an object

```c filename=heap_free_rejects_borrowed_access.c
struct item {
    int32 value;
};

int32 heap_free_rejects_borrowed_access(struct item* item) {
    free(item);
    return 0;
}
```

```click
verifying "heap_free_rejects_borrowed_access.c";

int32 heap_free_rejects_borrowed_access(struct item* item) {
    requires item != 0;
    views object(item);

    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: cannot free a pointer that is not a live heap allocation
```
