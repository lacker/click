# narrowing a viewable range refuses a range the order facts do not place inside it

The positive half is
`mdtests/have_viewable_prefix_of_a_range_in_a_c_proof.md`. Drop `k <= n` from it
and `a[0..k]` may run past the end of the stated range, so the narrowing is
refused. The diagnostic names the written goal and reports the failed
source-proof construction, without attributing the miss to a guessed source
range or byte-extent premise.

```c filename=have_loadable_prefix_rejects_a_range_outside_it_in_a_c_proof.c
int32 probe(int32 a[], int32 n, int32 k) {
    return 0;
}
```

```click
verifying "have_loadable_prefix_rejects_a_range_outside_it_in_a_c_proof.c";

int32 probe(int32 a[], int32 n, int32 k) {
    requires 0 <= k;
    requires viewable(a[0..n]);
    ensures result == 0;
} by {
    step();
    have viewable(a[0..k]);
    simp();
}
```

```expect
fail: no checked source proof was constructed for `viewable(
```
