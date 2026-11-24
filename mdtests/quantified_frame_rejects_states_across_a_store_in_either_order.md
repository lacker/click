# a quantified frame is refused in either direction across a store it cannot miss

Carrying a fact from the later state back to the earlier one crosses the
same store `v[j] = 1`, and the guard admits `j`. Both directions are
refused; this one reads `after` as the source.

```c filename=quantified_frame_rejects_states_across_a_store_in_either_order.c
void mark(int32 *v, int32 n, int32 j) {
    v[j] = 1;
}
```

```click
verifying "quantified_frame_rejects_states_across_a_store_in_either_order.c";

void mark(int32 *v, int32 n, int32 j) {
    requires 0 <= j;
    requires j < n;
    owns v[0..n];
    ensures forall (k: int32) { 0 <= k and k < n implies old(v[k]) == 1 };
} by {
    mark before;
    step();
    mark after;
    have forall (k: int32) { 0 <= k and k < n and k == j implies at(after, v[k]) == 1 };
    have forall (k: int32) { 0 <= k and k < n implies at(before, v[k]) == at(after, v[k]) } by { close(); }
}
```

```expect
fail: `solve` failed
```
