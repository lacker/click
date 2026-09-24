# Integer bytes copied onto a pointer field are not a pointer

This is the malformed-pointer negative of the byte-representation round trip.
An initialized, aligned `unsigned long` holds `4096`, and `memcpy` copies all
eight of its bytes onto the `int *target` field of a `struct record`. The
copy itself is a defined byte copy and is accepted: the representation-copy
effect plants the complete integer cell at `dst + 8`. What it does not do is
turn that integer into a pointer. The pointer load of `dst->target` meets an
integer cell and is refused as a load that does not fit the cell's value.

No pointer origin is guessed from the integer's bytes, and no allocation is
chosen for the address `4096`, so there is nothing for `*dst->target` to
dereference. The contract is irrelevant; execution stops at the load.

Companion: `byte_representation_pointer_bytes_as_integer_refused.md` refuses
the reverse reinterpretation, copying a pointer onto an integer field. The
same typed-load check refuses both.

```c filename=integer_bytes_as_pointer.c
void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);
struct record { unsigned int tag; int *target; };
int f(void) {
    unsigned long *word = malloc(sizeof(unsigned long));
    if (word == 0) { return -1; }
    struct record *dst = malloc(sizeof(struct record));
    if (dst == 0) { free(word); return -1; }
    *word = 4096ul;
    dst->tag = 1u;
    memcpy((unsigned char *)(void *)&dst->target, (unsigned char *)(void *)word, sizeof(unsigned long));
    int out = *dst->target;
    free(word); free(dst);
    return out;
}
```

```click
verifying "integer_bytes_as_pointer.c";

int f() {
    ensures result == 0 or result == -1;
} by {
    execute();
    simp();
}
```

```expect
fail: a 8-byte load at `heap-allocation:1000001@8` did not fit the cell's value
```
