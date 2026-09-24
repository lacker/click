# The frozen byte-representation round trip verifies

This is the import/load checkpoint for the P1
[byte-representation demo](../../issues/byte-representation-demo.md). The C
below is `examples/byte-representation/rep_copy.c`, byte for byte: a live `int`
pointee, a source record, a 16-byte buffer, and a distinct destination
record, with `memcpy` roundtripping all `sizeof(struct record)` bytes through
`(unsigned char *)(void *)` casts. The sidecar states the intended
`result == 18 or result == -1` contract, and it verifies: the scalar field
reads back `11`, the pointer field preserves its identity so `*dst->target`
reads `7`, and all four allocations free cleanly.

Two kernel rules compose to make this work. The representation-copy effect on
the standard-library `memcpy` declaration transfers each source cell whose
complete representation lies in the copied range, so the typed reloads see
the copied values through the untyped buffer. And resource normalization
never merges `allocation` tokens for structurally distinct blocks, so the
three live heap authorities stay unique through both copies and all four
frees. `mdtests/ext_memcpy_allocation_authority.md` pins the latter
independently with no typed values at all.

The negative, companion, scaling, and design-record halves of the issue
remain open; this fixture is the positive round trip only.

```c filename=rep_copy.c
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
    int out = dst->tag + *dst->target;
    free(pointee);
    free(src);
    free(buf);
    free(dst);
    return out;
}
```

```click
verifying "rep_copy.c";

int f() {
    ensures result == 18 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
