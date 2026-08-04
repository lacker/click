# free null is a no-op

```c filename=heap_free_null.c
int32 heap_free_null() {
    int32* pointer = 0;
    free(pointer);
    return 0;
}
```

```click
verifying "heap_free_null.c";

int32 heap_free_null() {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
