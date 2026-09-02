# sizeof supports scalar and pointer types

The C0 frontend lowers `sizeof` through the configured LP64 ABI for every
currently supported scalar and pointer type, not only struct tags.

```c filename=sizeof_supported_types.c
int32 sizeof_supported_types() {
    return sizeof(int32) + sizeof(uint8) + sizeof(int32*) + sizeof(uint8**);
}
```

```click
verifying "sizeof_supported_types.c";

int32 sizeof_supported_types() {
    ensures result == 21;
} by {
    execute();
    simp();
}
```

```expect
pass
```
