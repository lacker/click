# malloc result must be refined

The first allocation slice requires ordinary null-check control flow to decide
whether `malloc` created a block before the function can return without
handing the allocation result to its caller.

```c filename=heap_unchecked_allocation_result.c
struct item {
    int32 value;
};

int32 heap_unchecked_allocation_result() {
    struct item* item = malloc(sizeof(struct item));
    return 0;
}
```

```click
verifying "heap_unchecked_allocation_result.c";

int32 heap_unchecked_allocation_result() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: malloc result was neither refined by a null check nor returned
```
