# Opaque object pointers cannot be accessed without a typed conversion

```c filename=c_void_pointer_operations_rejected.c
int32 bad_dereference(void *value) {
    return *value;
}

void *bad_arithmetic(void *value) {
    return value + 1;
}
```

```click
verifying "c_void_pointer_operations_rejected.c";

int32 bad_dereference(void *value) {
    ensures result == 0;
}

void *bad_arithmetic(void *value) {
    ensures result == value;
}
```

```expect
fail: pointer operation has no known pointee type
```
