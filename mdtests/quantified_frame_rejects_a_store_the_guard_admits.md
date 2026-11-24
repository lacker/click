# a quantified frame does not carry a fact across a store its guard admits

`v[i] = 1` writes a cell that `0 <= k and k < n` admits, so the entry fact
`v[k] == 0` for every such `k` does not survive the store. The transport is
refused.

```c filename=quantified_frame_rejects_a_store_the_guard_admits.c
void mark(int32 *v, int32 n, int32 i) {
    v[i] = 1;
}
```

```click
verifying "quantified_frame_rejects_a_store_the_guard_admits.c";

void mark(int32 *v, int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    requires forall (k: int32) { 0 <= k and k < n implies v[k] == 0 };
    ensures forall (k: int32) { 0 <= k and k < n implies v[k] == 0 };
} by {
    have forall (k: int32) { 0 <= k and k < n implies old(v[k]) == 0 } by close();
    step();
    have forall (k: int32) { 0 <= k and k < n implies v[k] == 0 } by { close(); }
}
```

```expect
fail: `solve` failed
```
