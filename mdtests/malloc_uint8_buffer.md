# malloc supports byte-oriented buffers

The allocation builtin uses the target pointer's pointee type when checking
and reclaiming a byte buffer. This keeps `uint8` indexing and complete-access
`free` in the same one-byte coordinate system.

```c filename=malloc_uint8_buffer.c
uint8 malloc_uint8_buffer() {
    uint8* data = malloc(2 * sizeof(uint8));
    if (data == 0) {
        return 0;
    }
    data[0] = 42;
    uint8 result = data[0];
    free(data);
    return result;
}
```

```click
verifying "malloc_uint8_buffer.c";

uint8 malloc_uint8_buffer() {
    ensures result == 0 or result == 42 by auto;
}
```

```expect
pass
```
