# a store at byte 4 of an eight-byte cell is not framed

The word-boundary companion of `a_byte_store_inside_a_wide_cell_is_not_framed.md`,
which carries the explanation and the note on the byte view's place in the C
frontier. The store lands exactly four bytes in, where the cell's upper half
begins: the classic case where the address arithmetic looks like a clean
neighbouring word and the write is squarely inside an eight-byte read.

```c filename=byte_store_at_offset_4_is_not_framed.c
int64 stale_at_4(int64* q) {
    unsigned char* b;
    b = (unsigned char*)(void*) q;
    b[4] = 7;
    return *q;
}
```

```click
verifying "byte_store_at_offset_4_is_not_framed.c";

int64 stale_at_4(int64* q) {
    owns q[0..1];
    ensures result == old(q[0]);
}
```

```expect
fail: unclosed goal: result == old(q[0]); the two sides read the same address in different memory states (`result` reads the memory recorded at `statement(3).exit`; `old(q[0])` reads the function-entry memory); `q[0]` changed since function entry: the store to `q[…]` wrote it.
```
