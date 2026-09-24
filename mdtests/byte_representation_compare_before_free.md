# Comparing a restored pointer before its pointee is freed verifies

The passing control for `byte_representation_freed_pointer_compare_rejected.md`:
the same round trip, but `dst->target == pointee` is evaluated while
`pointee` is still live, and `free(pointee)` follows it. The restored pointer
keeps its allocation identity through both representation copies, so the
comparison is true and the contract verifies.

```c filename=compare_before_free.c
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
    int out = dst->target == pointee;
    free(pointee);
    free(src);
    free(buf);
    free(dst);
    return out;
}
```

```click
verifying "compare_before_free.c";

int f() {
    ensures result == 1 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
