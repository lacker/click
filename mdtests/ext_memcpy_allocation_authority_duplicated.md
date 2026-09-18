# An extern owned destination duplicates allocation authority

A minimal reproduction of a resource-accounting defect, unrelated to the byte
representation. Three live byte allocations, one `memcpy`, then `free` in
order. The first allocation is `malloc(4)` so the copy is a partial write into
the second; the third is untouched.

After the `memcpy`, the destination's `allocation` authority is held **twice**:
the proof context prints `owns allocation(heap-allocation:...@0, 16) (quantity
2)`. The later `free` of that block then reports the allocation as missing even
though the context displays it — `satisfies_fact` and
`contains_exact_representation` both return false for one unit, so the
quantity-2 fact is not usable.

The trigger is narrow. It needs all of:

- an `extern` contract that requires `owns destination[0..bytes]` **and**
  returns the destination pointer (`ensures result == destination`), and
- at least three live allocations at the call.

A single `memcpy` with two live allocations verifies; so does the same program
with no `memcpy`, and a custom extern with the identical `owns` requirement but
without `ensures result == destination`. The `bytes_equal` postcondition and
the checked representation-copy effect are not involved: only
`result == destination` changes the outcome.

See [`design/byte-representation/README.md`](../../design/byte-representation/README.md)
for how this blocks the frozen byte-representation probe.

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
fail: missing resource fact
```
