# A refused byte-range narrowing reports a source-proof failure

The contract does not establish `k <= n`. The requested byte prefix must be
refused. A failed smart construction reports that no checked source proof was
constructed; it must not guess which held range or missing premise caused it.

```click
theorem prefix_of_a_viewed_byte_range(v: uint8[], n: int32, k: int32) {
    views v[0..n];
    requires 0 <= k;
    ensures viewable(v[0..k]) by simp;
}
```

```expect
fail: no checked source proof was constructed for `viewable(
```
