# Read-only storage cannot be a copy destination

The storage-level companion of
[`byte_representation_readonly_copy_rejected.md`](byte_representation_readonly_copy_rejected.md),
which refuses a copy into mutable storage the function holds only a `views`
borrow of. Here the destination is a live `static const` table: read-only
storage with permanent read authority and no write authority at all. The
cast `(unsigned char *)table` is valid C, but the write `memcpy` would make
through it is undefined, and Click's C frontend refuses the const-discarding
conversion of the argument, before any copy is considered. The table keeps its
initializer, and no representation is copied into it.

```c filename=const_destination.c
void *memcpy(void *dest, const void *src, unsigned long n);
static const unsigned char table[4] = {1, 2, 3, 4};
unsigned char scratch[4];
int f(void) {
    scratch[0] = 9;
    scratch[1] = 9;
    scratch[2] = 9;
    scratch[3] = 9;
    memcpy((unsigned char *)table, scratch, 4);
    return table[0];
}
```

```click
verifying "const_destination.c";

int f() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: cannot discard const qualification from a pointer initializer
```
