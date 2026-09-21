# A byte store invalidates the wide cell whose bytes it overwrites

A `unsigned char *` view of an object may write any one of its bytes, so
`bytes[4] = 7` overwrites the fifth byte of the `int64` that `value` points
at. The `int64` read after it is not the value written before it, and the
claim that it is must be refused.

The addresses alone do not show this: `value + 4` is separate from `value`
by every address test the kernel has. The write has to be compared to the
cell by *bytes*, with the real width on both sides — one byte for the store,
eight for the `int64` cell it lands inside. A store that only forgot the
cell at its own address left this claim provable.

```c filename=a_byte_store_invalidates_the_wide_cell_it_covers.c
int64 read_after_byte_write(int64* value) {
    unsigned char* bytes;
    bytes = (unsigned char*)(void*) value;
    *value = 5;
    bytes[4] = 7;
    return *value;
}
```

```click
verifying "a_byte_store_invalidates_the_wide_cell_it_covers.c";

int64 read_after_byte_write(int64* value) {
    owns value[0..1];
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal: result == 5
```
