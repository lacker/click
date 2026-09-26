# a byte store into an element of a seeded constant range is not framed

The elements of `owns a[0..1000000]` are one run of seeded cells. A one-byte
store at byte 5 writes into element 1, so it drops that element from the run,
whose recorded value it no longer has, and leaves every other element alone.
The read of `a[1]` after it is therefore not its entry value, and
`result == old(a[1])` is refused. The C returns `a[1]` with its second byte
set to 7.

The positive companion reads `a[2]`, whose bytes the store misses, and keeps
its entry value.

```c filename=a_byte_store_into_a_constant_range_is_not_framed.c
int32 untouched_element(int32* a) {
    unsigned char* b;
    b = (unsigned char*)(void*) a;
    b[5] = 7;
    return a[2];
}

int32 stale_element(int32* a) {
    unsigned char* b;
    b = (unsigned char*)(void*) a;
    b[5] = 7;
    return a[1];
}
```

```click
verifying "a_byte_store_into_a_constant_range_is_not_framed.c";

int32 untouched_element(int32* a) {
    owns a[0..1000000];
    ensures result == old(a[2]);
} by {
    execute();
    simp();
}

int32 stale_element(int32* a) {
    owns a[0..1000000];
    ensures result == old(a[1]);
} by {
    execute();
    simp();
}
```

```expect
fail: result == old(a[1])
```
