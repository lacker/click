# external allocator contracts can return pointer-array storage

```c filename=external_pointer_array_allocator_contract.c
int32 caller() {
    uint8** slots;
    slots = external_alloc(8);
    slots[0] = 0;
    free(slots);
    return 1;
}
```

```click
verifying "external_pointer_array_allocator_contract.c";

extern uint8** external_alloc(int32 bytes) {
    requires 0 < bytes;
    ensures result != 0;
    produces allocation(result, bytes);
    produces result[0..1];
}

int32 caller() {
    ensures result == 1;
}
```

```expect
pass
```
