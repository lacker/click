# An out-of-bounds representation copy is refused

The `memcpy` contract requires `owns destination[0..bytes]` for the complete
copied extent. Copying 8 bytes into a 4-byte destination cannot satisfy that
requirement, so the call is refused at the access check before any byte moves.
Owning a smaller range does not stretch to cover a larger copy.

```c filename=out_of_bounds_memcpy.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);
int f(void) {
    unsigned char *src = malloc(16);
    if (src == 0) { return -1; }
    unsigned char *dst = malloc(4);
    if (dst == 0) { free(src); return -1; }
    memcpy(dst, src, 8);
    free(src); free(dst);
    return 0;
}
```

```click
verifying "out_of_bounds_memcpy.c";

int f() {
    ensures result == 0 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact
```
