# the order a wide store's refusal names is one that verifies

The positive companion of `a_wide_store_refusal_names_the_bytes_it_reaches.md`.
That refusal prints exactly one repair, `i < j`, and a diagnostic may only
print a repair that closes the goal it was printed for. This file is that
claim, checked: the same C and the same premises, with `i < j` stated in place
of `i != j`, verify.

The four-byte read at `a[i]` is then the lower of the two accesses, and it
fits inside the one-element gap the address ladder establishes. The eight-byte
store above it extends away from the gap, so its width cannot close it —
which is the asymmetry `one_element_gap_separates_bytes` turns on, and the
reason the refusal names this order and not the other one.

```c filename=an_index_order_separates_a_narrow_read_from_a_wide_store.c
int32 upper_half_survives(int32* a, int32 i, int32 j) {
    int64* w;
    a[i] = 5;
    w = (int64*)(void*) &a[j];
    *w = 0;
    return a[i];
}
```

```click
verifying "an_index_order_separates_a_narrow_read_from_a_wide_store.c";

int32 upper_half_survives(int32* a, int32 i, int32 j) {
    requires 0 <= j;
    requires j < 3;
    requires 0 <= i;
    requires i < 4;
    requires i < j;
    owns a[0..4];
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
pass
```
