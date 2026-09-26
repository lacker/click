# A refused byte-range narrowing names the stated range it started from

`viewable(v[0..k])` over `uint8` narrows the stated `views v[0..n]` only when
`0 <= k` and `k <= n` are facts. Here `k <= n` is not, and the refusal names
the stated range and the order fact it is waiting for, as it does for a range
of wider elements. A range of one-byte elements lowers its extent unscaled, so
the walk for a stated range to narrow from used to skip it for want of a
width, and the refusal claimed no range over `v` was stated anywhere.

```click
theorem prefix_of_a_viewed_byte_range(v: uint8[], n: int32, k: int32) {
    views v[0..n];
    requires 0 <= k;
    ensures viewable(v[0..k]) by { simp(); }
}
```

```expect
fail: narrowing that range needs `k <= n`
```
