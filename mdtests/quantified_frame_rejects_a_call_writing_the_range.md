# a call whose write set covers the quantified range is not framed

`fill` owns `v[0..n]` and writes `v[0]`, so the entry values of `v` do
not survive the call. The quantified frame is refused.

```c filename=quantified_frame_rejects_a_call_writing_the_range.c
void fill(int32 *v, int32 n) {
    v[0] = 1;
}

void caller(int32 *v, int32 n) {
    fill(v, n);
}
```

```click
verifying "quantified_frame_rejects_a_call_writing_the_range.c";

void fill(int32 *v, int32 n) {
    requires 0 < n;
    owns v[0..n];
}

void caller(int32 *v, int32 n) {
    requires 0 < n;
    owns v[0..n];
    ensures forall (k: int32) { 0 <= k and k < n implies v[k] == old(v[k]) };
} by {
    step();
    have forall (k: int32) { 0 <= k and k < n implies v[k] == old(v[k]) } by { close(); }
}
```

```expect
fail: `solve` failed
```
