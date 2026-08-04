# allocation authority is not memory access

Even exact lifetime authority plus ownership of one field is insufficient to
free the whole allocation.

```c filename=heap_free_requires_complete_access.c
struct item {
    int32 first;
    int32 second;
};

int32 heap_free_requires_complete_access(struct item* item) {
    free(item);
    return 0;
}
```

```click
verifying "heap_free_requires_complete_access.c";

int32 heap_free_requires_complete_access(struct item* item) {
    requires item != 0;
    consumes allocation(item, sizeof(struct item));
    consumes item->first;

    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact
```
