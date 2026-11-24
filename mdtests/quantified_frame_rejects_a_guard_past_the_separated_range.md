# a stated separation covers only the indices its range names

`separate(memory(a[0..1]), memory(a[1..2]))` holds for every `a`, and it
separates the store `a[1] = 7` from `a[0]` only. The guard `k < 2` admits
`k == 1`, which the store writes, so the quantified fact is refused.

```c filename=quantified_frame_rejects_a_guard_past_the_separated_range.c
void poke(int32 *a, int32 n) {
    a[1] = 7;
}
```

```click
verifying "quantified_frame_rejects_a_guard_past_the_separated_range.c";

void poke(int32 *a, int32 n) {
    requires 2 <= n;
    owns a[0..n];
    requires separate(memory(a[0..1]), memory(a[1..2]));
    ensures forall (k: int32) { 0 <= k and k < 2 implies a[k] == old(a[k]) };
} by {
    step();
    have forall (k: int32) { 0 <= k and k < 2 implies a[k] == old(a[k]) } by { close(); }
}
```

```expect
fail: `solve` failed
```
