# A field missing from a prefix copy cannot be read

Copying a prefix of a record's representation establishes only the cells that
prefix completely covers. Here 8 bytes cover `tag` (and padding) but not the
`target` pointer at offset 8, so reading `dst->target` afterwards is refused
as uninitialized. A partial representation copy never invents the missing
field's value or pointer identity.

This is the field-level companion to
[`byte_representation_partial_copy_frontier.md`](byte_representation_partial_copy_frontier.md),
which splits a single scalar instead of omitting a trailing field.

```c filename=incomplete_struct_memcpy.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);
struct record { unsigned int tag; int *target; };
int f(void) {
    int *pointee = malloc(sizeof(int));
    if (pointee == 0) { return -1; }
    struct record *src = malloc(sizeof(struct record));
    if (src == 0) { free(pointee); return -1; }
    struct record *dst = malloc(sizeof(struct record));
    if (dst == 0) { free(pointee); free(src); return -1; }
    *pointee = 7;
    src->tag = 11u;
    src->target = pointee;
    memcpy((unsigned char *)(void *)dst, (unsigned char *)(void *)src, 8);
    int out = *dst->target;
    free(pointee); free(src); free(dst);
    return out;
}
```

```click
verifying "incomplete_struct_memcpy.c";

int f() {
    ensures result == 7 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: read of uninitialized storage
```
