# Taking a declared object's address records its alignment

The compiler places a local at an address aligned for its type, so the
address-of expression carries that fact into C evaluation, where the masked
address compares equal to zero.

```c filename=aligned_from_local_address.c
int32 local_address_is_aligned() {
    int64 x = 0;
    return ((unsigned long)&x & 7) == 0;
}
```

```click
verifying "aligned_from_local_address.c";

int32 local_address_is_aligned() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
