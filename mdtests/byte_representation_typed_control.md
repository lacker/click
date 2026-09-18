# A typed field copy establishes the destination value

The typed control for the byte-representation scalar frontier. Two heap
records at the same allocation shapes as
[`byte_representation_scalar_copy_frontier.md`](byte_representation_scalar_copy_frontier.md),
the only difference being `dst->x = src->x` instead of a `sizeof`-wide
`memcpy`. This verifies, which isolates the frontier there to the
representation-copy rule: allocation refinement, null handling, ownership,
and the typed load are all in the shared part.

```c filename=typed_field_copy.c
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
    dst->x = src->x;
    int out = (int)dst->x;
    free(src);
    free(dst);
    return out;
}
```

```click
verifying "typed_field_copy.c";

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
