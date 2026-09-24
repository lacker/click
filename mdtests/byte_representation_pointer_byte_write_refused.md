# A byte write into a copied pointer loses the pointer

This is the frozen `rep_copy.c` round trip
(`examples/byte-representation/rep_copy.c`) with `buf[8] = 0;` between the two
copies: a defined write of the first byte of the copied `target` pointer.
The byte view updates integer cells in place, but a pointer cell has no byte
view, so the store forgets the pointer cell and records only the written
byte. The second copy then carries a one-byte cell, not a pointer, to
`dst->target`, and the eight-byte pointer load of `dst->target` is refused
because that byte does not fit a pointer. The overwritten pointer is not
reconstructed from its remaining bytes, and no pointer is fabricated from the
written one.

```c filename=pointer_byte_write.c
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
    buf[8] = 0;
    memcpy((unsigned char *)(void *)dst, buf, sizeof(struct record));
    int out = dst->tag + *dst->target;
    free(pointee);
    free(src);
    free(buf);
    free(dst);
    return out;
}
```

```click
verifying "pointer_byte_write.c";

int f() {
    ensures result == 18 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: a 8-byte load at `heap-allocation:1000003@8` did not fit the cell's value
```
