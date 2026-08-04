# allocation authority cannot be forgotten

The success path owns a live allocation at return and neither exports nor
frees it.

```c filename=heap_leak.c
struct item {
    int32 value;
};

int32 heap_leak() {
    struct item* item = malloc(sizeof(struct item));
    if (item == 0) {
        return -1;
    }
    item->value = 1;
    return 0;
}
```

```click
verifying "heap_leak.c";

int32 heap_leak() {
    ensures result == -1 or result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: live allocation obligation was neither returned nor freed
```
