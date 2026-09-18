# The byte-representation scalar frontier stops at the typed reload

This is the scalar reduction of the
[byte-representation demo](../../issues/byte-representation-demo.md)
frontier in [`rep_copy.c`](../../design/byte-representation/rep_copy.c). Two
heap records, one initialized to `7`, one copied from the other with a
`sizeof`-wide `memcpy`. The intended postcondition is `result == 7 or result
== -1`, and every needed fact is present after the copy: both blocks owned,
the source cell initialized, and `bytes_equal(dst, 0, old(src), 0, 4)`.

`execute()` nevertheless stops at the `dst->x` typed load: owning bytes that
equal an initialized source's bytes does not establish the destination's
typed value. [`byte_representation_typed_control.md`](byte_representation_typed_control.md)
is the same program with `dst->x = src->x` and it verifies, so the missing
piece is the representation-copy rule, not allocation or ownership handling.

```c filename=scalar_memcpy_frontier.c
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
verifying "scalar_memcpy_frontier.c";

int h() {
    ensures result == 7 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: read of uninitialized storage
```
