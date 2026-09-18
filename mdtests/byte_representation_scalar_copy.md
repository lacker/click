# A typed field copy across memcpy preserves the scalar value

A direct, byte-exact `memcpy` between two heap records establishes the
destination's typed value from the source's initialized cell. The copy covers
the complete representation of `x`, so the destination observation `dst->x` is
the source value `7`.

[`byte_representation_typed_control.md`](byte_representation_typed_control.md)
is the same program with `dst->x = src->x`. Both verify, so the copy mechanism
is no longer what distinguishes them: a byte copy of a complete, initialized
cell and a typed field copy now establish the same observation.

This is the direct-copy half of the
[byte-representation demo](../../issues/byte-representation-demo.md). The
intermediate untyped buffer in
[`design/byte-representation/rep_copy.c`](../../design/byte-representation/rep_copy.c)
and the pointer-provenance negatives remain open.

```c filename=scalar_memcpy.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);
struct box { unsigned int x; };
int h(void) {
    struct box *src = malloc(sizeof(struct box));
    if (src == 0) { return -1; }
    struct box *dst = malloc(sizeof(struct box));
    if (dst == 0) { free(src); return -1; }
    src->x = 7u;
    memcpy((unsigned char *)(void *)dst, (unsigned char *)(void *)src, sizeof(struct box));
    int out = (int)dst->x;
    free(src);
    free(dst);
    return out;
}
```

```click
verifying "scalar_memcpy.c";

int h() {
    ensures result == 7 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
