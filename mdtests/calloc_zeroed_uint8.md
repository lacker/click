# calloc zeroes byte-oriented buffers

The zeroed allocation model applies to a `uint8*` target as well as the
existing int32 and struct targets. The byte-width range must also be consumed
when the buffer is freed.

```c filename=calloc_zeroed_uint8.c
uint8 calloc_zeroed_uint8() {
    uint8* data = calloc(2, sizeof(uint8));
    if (data == 0) {
        return 1;
    }
    uint8 result = data[0];
    free(data);
    return result;
}
```

```click
verifying "calloc_zeroed_uint8.c";

uint8 calloc_zeroed_uint8() {
    ensures result == 0 or result == 1 by auto;
}
```

```expect
pass
```
