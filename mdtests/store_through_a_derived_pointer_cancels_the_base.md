# A store through a derived pointer names its element relative to the owner

`b` is `a + k`, so `b[1]` is the element `k + 1` of `a`. Its byte offset is
`(a + 4k) + 4`, and the store's resource range is that offset less `a`'s own:
the two copies of `a`'s base cancel exactly, because pointer offsets are
exact sums, and leave the element index `k + 1`. The held `owns a[0..1000]`
covers it because `5 <= k < 999`.

Without the cancellation the store asked for `owns a[((a + k) + 1) - a]`,
an index the range checker could not bound, and was refused.
`store_through_a_derived_pointer_out_of_range.md` is the negative: there the
bound on `k` does not keep `k + 1` inside the range.

```c filename=store_through_a_derived_pointer_cancels_the_base.c
void put(int32* a, int32 k) {
    int32* b = a + k;
    b[1] = 7;
}
```

```click
verifying "store_through_a_derived_pointer_cancels_the_base.c";

void put(int32* a, int32 k) {
    owns a[0..1000];
    requires 5 <= k and k < 999;
    ensures a[0] == old(a[0]);
    ensures a[k] == old(a[k]);
} by {
    execute();
    simp();
}
```

```expect
pass
```
