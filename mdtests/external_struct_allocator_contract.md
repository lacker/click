# external allocator contracts can return struct storage

```c filename=external_struct_allocator_contract.c
struct item {
    int32 value;
    int32 other;
};

int32 caller() {
    int32 result;
    struct item* item;
    item = external_alloc(8);
    item->value = 7;
    item->other = 9;
    result = item->value;
    free(item);
    return result;
}
```

```click
verifying "external_struct_allocator_contract.c";

extern struct item* external_alloc(int32 bytes) {
    requires 0 < bytes;
    ensures result != 0;
    produces allocation(result, bytes);
    produces result[0..2];
}

int32 caller() {
    ensures result == 7;
}
```

```expect
pass
```
