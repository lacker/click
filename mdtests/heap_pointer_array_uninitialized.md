# fresh pointer-array cells are uninitialized

Pointer-array allocation grants ownership of the cells but does not invent a
pointer value for a cell that has not been stored.

```c filename=heap_pointer_array_uninitialized.c
int32* heap_pointer_array_uninitialized() {
    int32** slots = malloc(sizeof(int32*));
    if (slots == 0) {
        return 0;
    }
    return slots[0];
}
```

```click
verifying "heap_pointer_array_uninitialized.c";

int32* heap_pointer_array_uninitialized() {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
