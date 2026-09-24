# A restored pointer does not authorize its pointee

[`byte_representation_symbolic_roundtrip.md`](byte_representation_symbolic_roundtrip.md)
without the caller's `views p[0..1]` clause (and the bounds that mention
`p[0]`). The byte round trip still restores `dst->target` with its identity,
which is why the refusal names `p`: the load of `*dst->target` needs
authority over `p[0..1]`, and nothing in the function holds it. Copying a
pointer's representation copies the address and its allocation identity,
never its pointee's resource.

```c filename=restored_pointer_needs_authority.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);

struct record {
    unsigned int tag;
    int *target;
};

int g(unsigned int tag, int *p, int **restored) {
    struct record *src = malloc(sizeof(struct record));
    if (src == 0) {
        return -1;
    }
    unsigned char *buf = malloc(16);
    if (buf == 0) {
        free(src);
        return -1;
    }
    struct record *dst = malloc(sizeof(struct record));
    if (dst == 0) {
        free(src);
        free(buf);
        return -1;
    }
    src->tag = tag;
    src->target = p;
    memcpy(buf, (unsigned char *)(void *)src, sizeof(struct record));
    memcpy((unsigned char *)(void *)dst, buf, sizeof(struct record));
    *restored = dst->target;
    int out = dst->tag + *dst->target;
    free(src);
    free(buf);
    free(dst);
    return out;
}
```

```click
verifying "restored_pointer_needs_authority.c";

int32 g(uint32 tag, int32 *p, int32 **restored) {
    owns restored[0..1];
    requires tag <= 1000;
    ensures result == -1 or restored[0] == p;
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `views p[0..1]`
```
