# Comparing a restored pointer after its pointee is freed is refused

This is the frozen `rep_copy.c` round trip
(`byte_representation_roundtrip.md`) with its final read replaced: after
`free(pointee)`, the function returns whether the restored `dst->target`
still equals `pointee`. The contract claims the comparison is true, and until
the freed-pointer rule it verified, because the representation copy preserves
the pointer's allocation identity.

Under C11 6.2.4p2 both pointers' values became indeterminate when `pointee`
was freed, and Annex J.2 makes using such a value, a comparison included,
undefined behavior. Loading `dst->target` out of the destination record is
not itself the use; the `==` is. The kernel refuses it and names the freed
allocation. `byte_representation_compare_before_free.md` is the passing
control that compares the two pointers while `pointee` is still live.

```c filename=freed_pointer_compare.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);

struct record {
    unsigned int tag;
    int *target;
};

int f(void) {
    int *pointee = malloc(sizeof(int));
    if (pointee == 0) {
        return -1;
    }
    struct record *src = malloc(sizeof(struct record));
    if (src == 0) {
        free(pointee);
        return -1;
    }
    unsigned char *buf = malloc(16);
    if (buf == 0) {
        free(pointee);
        free(src);
        return -1;
    }
    struct record *dst = malloc(sizeof(struct record));
    if (dst == 0) {
        free(pointee);
        free(src);
        free(buf);
        return -1;
    }
    *pointee = 7;
    src->tag = 11u;
    src->target = pointee;
    memcpy(buf, (unsigned char *)(void *)src, sizeof(struct record));
    memcpy((unsigned char *)(void *)dst, buf, sizeof(struct record));
    free(pointee);
    int out = dst->target == pointee;
    free(src);
    free(buf);
    free(dst);
    return out;
}
```

```click
verifying "freed_pointer_compare.c";

int f() {
    ensures result == 1 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: use of a pointer into freed allocation heap-allocation:1000000
```
