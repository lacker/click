# Pointer bytes copied onto an integer field are not an integer

The reverse of
[`byte_representation_integer_bytes_as_pointer_refused.md`](byte_representation_integer_bytes_as_pointer_refused.md).
A `struct record` whose `target` field points at a live `int` is copied, all
`sizeof(struct record)` bytes, onto a `struct word_record` whose field at the
same offset is an `unsigned long`. The copy plants the complete pointer cell
at `dst + 8`, preserving its allocation identity, but a pointer's
representation has no integer value in Click's model. The eight-byte integer
load of `dst->bits` meets a pointer cell and is refused as a load that does
not fit the cell's value; no address is invented for the pointer.

Both directions are the same kernel rule: a typed load accepts only a cell of
its own value kind, and a representation copy moves cells without converting
them. The contract is irrelevant; execution stops at the load.

```c filename=pointer_bytes_as_integer.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);
struct record { unsigned int tag; int *target; };
struct word_record { unsigned int tag; unsigned long bits; };
int f(void) {
    int *pointee = malloc(sizeof(int));
    if (pointee == 0) { return -1; }
    struct record *src = malloc(sizeof(struct record));
    if (src == 0) { free(pointee); return -1; }
    struct word_record *dst = malloc(sizeof(struct word_record));
    if (dst == 0) { free(pointee); free(src); return -1; }
    *pointee = 7;
    src->tag = 11u;
    src->target = pointee;
    memcpy((unsigned char *)(void *)dst, (unsigned char *)(void *)src, sizeof(struct record));
    int out = dst->bits != 0ul;
    free(pointee); free(src); free(dst);
    return out;
}
```

```click
verifying "pointer_bytes_as_integer.c";

int f() {
    ensures result == 1 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: a 8-byte load at `heap-allocation:1000002@8` did not fit the cell's value
```
