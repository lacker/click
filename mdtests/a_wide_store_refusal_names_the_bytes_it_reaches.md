# a wide store's refusal names the bytes it reaches, not the indexes

`a_wide_store_reaches_the_narrow_cell_beside_it.md` is the soundness half of
this shape: an eight-byte store at `a[j]` in a four-byte array covers `a[j]`
and `a[j + 1]`, so `i != j` does not frame `a[i]` across it, and the kernel
stopped letting an address ladder answer the byte question alone.

This file is the diagnostic half. The refusal that shipped with that fix still
said

    the store to `a[j]` may have written it. If `i` and `j` differ, state `i != j`.

and `i != j` is already stated here — it is the premise the reader wrote in
response to that very sentence, and it is not what is missing. A refusal that
names a repair the reader has already applied says nothing about what was
actually compared, which is bytes: the store's eight against the element's
four.

So the text now names the store's width, the object's element width, how many
elements the store therefore covers, and why the disequality rules out only
the first of them. The repair it prints is the one the gap rule actually
clears. `one_element_gap_separates_bytes` establishes a gap of one element
from an address ladder; a bare disequality leaves the direction open, so both
accesses must fit in it, and the eight-byte store does not. A *strict order*
fixes the direction, and then only the lower access has to fit — the upper one
extends away from the gap. `i < j` puts the four-byte read below the store, so
it fits, and the proof closes.

`an_index_order_separates_a_narrow_read_from_a_wide_store.md` is that repair,
verifying. The other direction, `j + 1 < i`, is true of the addresses and is
*not* offered: it puts the eight-byte store below the gap, which the rule
cannot clear, so printing it would send the reader to state a premise that
does not close the goal.

```c filename=a_wide_store_refusal_names_the_bytes_it_reaches.c
int32 upper_half_survives(int32* a, int32 i, int32 j) {
    int64* w;
    a[i] = 5;
    w = (int64*)(void*) &a[j];
    *w = 0;
    return a[i];
}
```

```click
verifying "a_wide_store_refusal_names_the_bytes_it_reaches.c";

int32 upper_half_survives(int32* a, int32 i, int32 j) {
    requires 0 <= j;
    requires j < 3;
    requires 0 <= i;
    requires i < 4;
    requires i != j;
    owns a[0..4];
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: `a[i]` may have changed since earlier in this function: the store to `a[j]` writes 8 bytes where `a` has 4-byte elements, so it covers the 2 elements from `a[j]` up and `i != j` rules out only the first of them. State `i < j`, which puts `a[i]` below every byte the store writes.
```
