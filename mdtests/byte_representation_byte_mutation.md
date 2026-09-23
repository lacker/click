# A defined byte mutation proves the changed observation

This is the frozen `rep_copy.c` round trip
(`design/byte-representation/rep_copy.c`) with one defined byte write between
the two copies: `buf[0] = 1;` overwrites the low byte of the copied `tag`.
Under the target's little-endian byte order the kernel updates the typed
`unsigned int` cell at buffer offset 0 in place,
`(v & ~0xFF) | 1`, instead of forgetting it, so the second copy carries the
changed tag into `dst` and the observation becomes `1 + 7 == 8`.

The pointer cell at buffer offset 8 is untouched, so `*dst->target` still
reads the live pointee. The original `result == 18` contract would now be
false; this fixture proves the changed one.

```c filename=byte_mutation.c
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
    buf[0] = 1;
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
verifying "byte_mutation.c";

int f() {
    ensures result == 8 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
