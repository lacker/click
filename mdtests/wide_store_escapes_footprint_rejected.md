# A wide retyping cast is outside the supported C0 memory model

```c filename=wide_store_escapes_footprint_rejected.c
int32 wide_store(uint8* b) {
    int32* w;
    w = (int32*) b;
    w[1] = 7;
    return 0;
}

uint8 caller(uint8* b) {
    int32 ignored;
    ignored = wide_store(b);
    return b[7];
}
```

```click
verifying "wide_store_escapes_footprint_rejected.c";

int32 wide_store(uint8* b) {
    views b[0..8];
    owns b[0..5];
    ensures result == 0;
} by {
    execute();
    simp();
}

uint8 caller(uint8* b) {
    views b[0..8];
    owns b[0..5];
    ensures result == old(b[7]);
} by {
    execute();
    simp();
}
```

```expect
fail: retyping object-pointer casts are unsupported
```
