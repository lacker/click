# external allocator contracts return owned storage

```c filename=external_allocator_contract.c
int32 caller() {
    uint8* data;
    data = external_alloc(4);
    data[0] = 7;
    free(data);
    return 7;
}
```

```click
verifying "external_allocator_contract.c";

extern uint8* external_alloc(int32 bytes) {
    requires 0 < bytes;
    ensures result != 0;
    produces allocation(result, bytes);
    produces result[0..bytes];
}

int32 caller() {
    ensures result == 7;
}
```

```expect
pass
```
