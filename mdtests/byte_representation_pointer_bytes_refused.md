# A byte of a copied pointer is not readable

This is the frozen `rep_copy.c` round trip
(`design/byte-representation/rep_copy.c`) cut after its first `memcpy`, reading
`buf[8]`: the first byte of the copied `target` pointer. The representation
copy planted that field as a typed pointer cell at buffer offset 8, and a
pointer's bytes are opaque. The byte view of integer cells covers integer
cells only, so the one-byte load at the pointer cell's own address is refused
as a load that does not fit the cell's value. Nothing is guessed about the
address's bytes, which is what keeps a pointer rebuilt from bytes refused.
The contract is irrelevant; execution stops at the load.

Companion: `byte_representation_pointer_byte_write_refused.md` refuses the
write direction.

```c filename=pointer_byte_read.c
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
    int out = buf[8];
    free(pointee);
    free(src);
    free(buf);
    free(dst);
    return out;
}
```

```click
verifying "pointer_byte_read.c";

int f() {
    ensures result == 0 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: a 1-byte load at `heap-allocation:1000002@8` did not fit the cell's value
```
