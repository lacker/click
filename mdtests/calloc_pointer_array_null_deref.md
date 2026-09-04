# zeroed pointer-array cells are null, not dereferenceable

`calloc` initializes a pointer cell to null. Reading the cell is defined, but
dereferencing that null pointer remains invalid.

```c filename=calloc_pointer_array_null_deref.c
int32 calloc_pointer_array_null_deref() {
    int32** slots = calloc(1, sizeof(int32*));
    if (slots == 0) {
        return 0;
    }
    return *slots[0];
}
```

```click
verifying "calloc_pointer_array_null_deref.c";

int32 calloc_pointer_array_null_deref() {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact
```
