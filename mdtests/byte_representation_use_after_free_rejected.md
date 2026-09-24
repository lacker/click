# A restored pointer does not restore a freed pointee

This is the frozen `rep_copy.c` round trip
(`byte_representation_roundtrip.md`) with one change: `free(pointee)`
moves before the final read, so `*dst->target` dereferences the restored
pointer after its pointee's lifetime has ended. The representation copy
preserves the pointer's allocation identity, which is exactly why the load is
refused: `dst->target` still names the freed allocation, and the kernel
reports the load as an invalid memory access. Copying a pointer's
representation neither extends its pointee's lifetime nor carries authority
to access it.

```c filename=restored_pointer_after_free.c
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
    memcpy((unsigned char *)(void *)dst, buf, sizeof(struct record));
    free(pointee);
    int out = dst->tag + *dst->target;
    free(src);
    free(buf);
    free(dst);
    return out;
}
```

```click
verifying "restored_pointer_after_free.c";

int f() {
    ensures result == 18 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: invalid memory access
```
