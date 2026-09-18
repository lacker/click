# The frozen byte-representation probe stops after the typed reload

This is the import/load checkpoint for the P1
[byte-representation demo](../../issues/byte-representation-demo.md). The C
below is `design/byte-representation/rep_copy.c`, byte for byte: a live `int`
pointee, a source record, a 16-byte buffer, and a distinct destination
record, with `memcpy` roundtripping all `sizeof(struct record)` bytes through
`(unsigned char *)(void *)` casts. The sidecar states the intended
`result == 18 or result == -1` contract. It is not evidence that the
roundtrip verifies; it pins the current bounded proof frontier.

The direct-copy representation rule now carries the typed reload through both
`memcpy` calls: `dst->tag` and `dst->target` read the copied values, so the
frozen probe advances to its `free` sequence. It then stops on a pre-existing
allocation-resource gap unrelated to the byte model: an `extern` contract's
`owns destination[0..bytes]` over an allocation-backed buffer duplicates the
allocation authority, so a later `free` reports a missing `owns
allocation(...)` fact. The minimal reduction is two byte buffers with no typed
values at all:

```text
unsigned char *a = malloc(4);
unsigned char *b = malloc(16);
unsigned char *c = malloc(16);
memcpy(b, a, 4);
memcpy(c, b, 16);
free(a); free(b); free(c);
```

That allocation gap is the next blocker for this probe; the pointer half and
the buffer hop's representation carrier remain in the issue.

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
fail: missing resource fact
```
