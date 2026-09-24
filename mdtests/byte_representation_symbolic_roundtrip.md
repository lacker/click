# A symbolic scalar and a caller's pointer survive a byte round trip

The parameterized companion of the frozen round trip
(`byte_representation_roundtrip.md`), which proves the claim for constant
field values. Here `g` receives an arbitrary `tag` and a caller-supplied
`int *p`, stores both into a heap `struct record`, copies all
`sizeof(struct record)` bytes into a 16-byte heap buffer and from there into
a distinct heap record, then reads the restored fields. It reports the
restored pointer through `restored` before freeing the destination, and
returns `dst->tag + *dst->target`.

The contract states the three facts the round trip must preserve:

- exact scalar equality: the returned sum is `tag + p[0]`, so the restored
  `tag` field equals the symbolic argument;
- pointer identity: the restored `target` field is `p` itself, not merely
  a pointer to an equal value;
- the pointee observation: `*dst->target` reads `p[0]`.

The pointee load is authorized only by the caller's `views p[0..1]`; the
function owns none of `p`'s storage, and the copy does not create any.
Without that clause the same load is refused
([`byte_representation_restored_pointer_needs_authority.md`](byte_representation_restored_pointer_needs_authority.md)).
The `tag <= 1000` and `0 <= p[0] <= 1000` bounds keep the C sum and its
conversion to `int` in range, so the sum is exact and the successful result
is never `-1`: `result == -1` holds exactly on the allocation-failure paths,
where `restored` is left untouched.

```c filename=symbolic_roundtrip.c
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
verifying "symbolic_roundtrip.c";

int32 g(uint32 tag, int32 *p, int32 **restored) {
    views p[0..1];
    owns restored[0..1];
    requires tag <= 1000;
    requires 0 <= p[0];
    requires p[0] <= 1000;
    ensures result == -1 or result == tag + p[0];
    ensures result == -1 or restored[0] == p;
} by {
    execute();
    simp();
}
```

```expect
pass
```
