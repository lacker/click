# excluding the first store does not exclude the second

`k != i` excludes the store to `v[i]`, but not the store to `v[j]`, and
`j` may be any index. The quantified frame across both stores is refused.

```c filename=quantified_frame_rejects_a_second_store_the_guard_admits.c
void mark(int32 *v, int32 n, int32 i, int32 j) {
    v[i] = 1;
    v[j] = 2;
}
```

```click
verifying "quantified_frame_rejects_a_second_store_the_guard_admits.c";

void mark(int32 *v, int32 n, int32 i, int32 j) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= j;
    requires j < n;
    owns v[0..n];
    ensures forall (k: int32) { 0 <= k and k < n and k != i implies v[k] == old(v[k]) };
} by {
    step();
    step();
    have forall (k: int32) { 0 <= k and k < n and k != i implies v[k] == old(v[k]) } by { close(); }
}
```

```expect
fail: `solve` failed
```
