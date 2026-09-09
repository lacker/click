# A byte retyping cast is outside the supported C0 memory model

```c filename=byte_store_leaves_word_stale_rejected.c
int32 byte_store_alias() {
    int32 x = 16909060;
    uint8* b = (uint8*)&x;
    b[1] = 0;
    return x;
}
```

```click
verifying "byte_store_leaves_word_stale_rejected.c";

int32 byte_store_alias() {
    ensures result == 16909060;
}
```

```expect
fail: retyping object-pointer casts are unsupported
```
