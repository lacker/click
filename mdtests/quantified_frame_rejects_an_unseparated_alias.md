# distinct parameter names do not separate a quantified read from a store

Nothing separates `a` from `b`, and a caller may pass one array as both.
The store `b[j] = 1` may then write `a[j]`, so the quantified frame is
refused.

```c filename=quantified_frame_rejects_an_unseparated_alias.c
void mark_other(int32 *a, int32 *b, int32 j, int32 n) {
    b[j] = 1;
}
```

```click
verifying "quantified_frame_rejects_an_unseparated_alias.c";

void mark_other(int32 *a, int32 *b, int32 j, int32 n) {
    requires 0 <= j;
    requires j < n;
    owns b[0..n];
    ensures forall (k: int32) { 0 <= k and k < n implies a[k] == old(a[k]) };
} by {
    step();
    have forall (k: int32) { 0 <= k and k < n implies a[k] == old(a[k]) } by { close(); }
}
```

```expect
fail: `solve` failed
```
