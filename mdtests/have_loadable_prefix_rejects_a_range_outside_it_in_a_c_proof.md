# narrowing a loadable range refuses a range the order facts do not place inside it

The positive half is
`mdtests/have_loadable_prefix_of_a_range_in_a_c_proof.md`. Drop `k <= n` from it
and `a[0..k]` may run past the end of the stated range, so the narrowing is
refused — and the refusal names the goal and the stated range the way the proof
wrote them, and the one order fact that would place one inside the other.

A refusal naming the lowered form instead, `loadable(base=the pointer value at
this program point, bytes=(v2 * 4))`, is what this reports if the diagnostic
regresses: it tells the reader neither which range they asked for nor what to go
and prove.

```c filename=have_loadable_prefix_rejects_a_range_outside_it_in_a_c_proof.c
int32 probe(int32 a[], int32 n, int32 k) {
    return 0;
}
```

```click
verifying "have_loadable_prefix_rejects_a_range_outside_it_in_a_c_proof.c";

int32 probe(int32 a[], int32 n, int32 k) {
    requires 0 <= k;
    requires loadable(a[0..n]);
    ensures result == 0;
} by {
    step();
    have loadable(a[0..k]) by { simp(); }
    simp();
}
```

```expect
fail: `loadable(a[0..k])` does not follow from `loadable(a[0..n])`: narrowing that range needs `k <= n`, which is not an available fact
```
