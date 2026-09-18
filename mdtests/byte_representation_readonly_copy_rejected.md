# A read-only borrow cannot authorize a representation copy

`memcpy` requires `owns destination[0..bytes]`: a copy needs write authority,
not just readability. A function that only `views` a buffer holds a stable
borrow for the call — enough to read, never enough to overwrite. The copy is
refused at the ownership precondition; the borrow is not upgraded and no
representation is established.

```c filename=readonly_memcpy.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);
unsigned char buf[16];
int f(unsigned char *src) {
    memcpy(buf, src, 16);
    return buf[0];
}
```

```click
verifying "readonly_memcpy.c";

int f(uint8 src[]) {
    requires loadable(src[0..16]);
    views buf[0..16];
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns global:buf@0[0..16]`
```
