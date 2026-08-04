# fresh heap storage is uninitialized

Allocation grants ownership but does not invent values for bytes that have not
been stored yet.

```c filename=heap_uninitialized_read.c
struct item {
    int32 value;
};

int32 heap_uninitialized_read() {
    struct item* item = malloc(sizeof(struct item));
    if (item == 0) {
        return -1;
    }
    return item->value;
}
```

```click
verifying "heap_uninitialized_read.c";

int32 heap_uninitialized_read() {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
