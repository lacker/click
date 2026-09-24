# A padding byte of a copied record is not observable

This is the frozen `rep_copy.c` round trip
(`examples/byte-representation/rep_copy.c`) cut after its first `memcpy`,
reading `buf[4]`: the first of the four padding bytes between the four-byte
`tag` at offset 0 and the eight-byte `target` at offset 8. The representation
copy moves typed cells, and padding has no cell, so the buffer holds nothing
at offset 4 and the byte load is refused as a read of uninitialized storage.

C11 gives padding bytes unspecified values. Click assigns them none: the read
is refused rather than returning an invented or arbitrary byte, so no proof
can depend on a padding byte's value, and nothing about a whole record's
bytes, padding included, follows from equality of its fields. The contract is irrelevant;
execution stops at the load.

```c filename=padding_byte_read.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);

struct record {
    unsigned int tag;
    int *target;
};

int f(void) {
    int *pointee = malloc(sizeof(int));
    if (pointee == 0) {
        return -1;
    }
    struct record *src = malloc(sizeof(struct record));
    if (src == 0) {
        free(pointee);
        return -1;
    }
    unsigned char *buf = malloc(16);
    if (buf == 0) {
        free(pointee);
        free(src);
        return -1;
    }
    struct record *dst = malloc(sizeof(struct record));
    if (dst == 0) {
        free(pointee);
        free(src);
        free(buf);
        return -1;
    }
    *pointee = 7;
    src->tag = 11u;
    src->target = pointee;
    memcpy(buf, (unsigned char *)(void *)src, sizeof(struct record));
    int out = buf[4];
    free(pointee);
    free(src);
    free(buf);
    free(dst);
    return out;
}
```

```click
verifying "padding_byte_read.c";

int f() {
    ensures result == 0 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: read of uninitialized storage
```
