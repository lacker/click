# A partial representation copy does not establish the typed value

The representation-copy rule only transfers a source cell whose complete byte
representation lies inside the copied range. A copy of 2 bytes into the first
half of a fresh `unsigned int` would split the source cell, so nothing is
planted: the destination keeps its fresh allocation's uninitialized bytes with
no `unsigned int` value, and the `dst->x` load is refused as uninitialized.
The proof explicitly composes the destination's two returned byte ranges
before attempting that typed load. This guards the rule against establishing
an observation from a split cell, independently of ownership fragmentation.

```c filename=scalar_partial_memcpy.c
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
    memcpy((unsigned char *)(void *)dst, (unsigned char *)(void *)src, 2);
    int out = (int)dst->x;
    free(src);
    free(dst);
    return out;
}
```

```click
verifying "scalar_partial_memcpy.c";
resource Whole(p: struct box*) { owns *p; }

int h() {
    ensures result == 7 or result == -1;
} by {
    step(); step();
    branch { true => { step(); close(); } false => {} }
    step(); step();
    branch { true => { step(); step(); close(); } false => {} }
    step(); step();
    fold(Whole(dst));
    unfold(Whole(dst));
}
```

```expect
fail: read of uninitialized storage
```
