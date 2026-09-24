# Bytes of a copied integer read back through the buffer

The C below is the frozen `rep_copy.c` round trip
(`examples/byte-representation/rep_copy.c`) cut after its first `memcpy`: the
record's bytes are in the `unsigned char` buffer, and each function reads one
of them. The representation copy planted `tag` as a typed `unsigned int` cell
at buffer offset 0, so `buf[0]` and `buf[1]` land inside that cell rather than
on cells of their own.

The kernel's byte view of integer cells answers them. Under the selected
target's little-endian byte order, byte `k` of an integer cell is
`(v >> 8k) & 0xFF`, so `buf[0]` reads `11` and `buf[1]` reads `0`. The view is
a bounded lookup of the containing cell in the buffer's own block; it is
target-dependent, and a big-endian environment has no view at all.

```c filename=byte_read.c
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
    int out = buf[0];
    free(pointee);
    free(src);
    free(buf);
    free(dst);
    return out;
}

int g(void) {
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
    int out = buf[1];
    free(pointee);
    free(src);
    free(buf);
    free(dst);
    return out;
}
```

```click
verifying "byte_read.c";

int f() {
    ensures result == 11 or result == -1;
} by {
    execute();
    simp();
}

int g() {
    ensures result == 0 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
