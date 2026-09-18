# An extern owned destination keeps allocation authority unique

Three live byte allocations, one `memcpy`, then `free` in order. The first
allocation is `malloc(4)` so the copy is a partial write into the second; the
third is untouched. Each block's `allocation` authority stays exactly one
unit through the call and the frees, so all three free cleanly.

This is a regression for a resource-accounting defect in which the
destination's `allocation` was held twice after the copy (the context printed
quantity 2) and the later `free` reported it missing. The defect needed an
`extern` contract that requires `owns destination[0..bytes]` and returns the
destination pointer, plus at least three live allocations. Its root cause was
unsound, not merely imprecise: resource normalization merged two `allocation`
tokens for structurally distinct heap blocks because a `Constant(false)`
contradiction fact in the assumptions made distinct pointers compare equal.
The kernel now refuses to equate blocks it proves distinct, so no assumption
can merge distinct allocations.

See [`design/byte-representation/README.md`](../../design/byte-representation/README.md)
for the frozen probe this unblocks.

```c filename=memcpy_allocation_authority.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);
int f(void) {
    unsigned char *a = malloc(4);
    if (a == 0) { return -1; }
    unsigned char *b = malloc(16);
    if (b == 0) { free(a); return -1; }
    unsigned char *c = malloc(16);
    if (c == 0) { free(a); free(b); return -1; }
    memcpy(b, a, 4);
    free(a); free(b); free(c);
    return 0;
}
```

```click
verifying "memcpy_allocation_authority.c";

int f() {
    ensures result == 0 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
