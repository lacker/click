# A store through a derived pointer past the owned range is refused

The negative of `store_through_a_derived_pointer_cancels_the_base.md`. With
`k < 1000` the element `k + 1` that `b[1]` writes can be `1000`, one past
`owns a[0..1000]`, so the store is refused. The refusal names the element
relative to `a`, as `k + 1`, with no trace of `a`'s own base.

```c filename=store_through_a_derived_pointer_out_of_range.c
void put(int32* a, int32 k) {
    int32* b = a + k;
    b[1] = 7;
}
```

```click
verifying "store_through_a_derived_pointer_out_of_range.c";

void put(int32* a, int32 k) {
    owns a[0..1000];
    requires 5 <= k and k < 1000;
    ensures a[0] == old(a[0]);
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns a[(k + 1)..((k + 1) + 1)]`
```
