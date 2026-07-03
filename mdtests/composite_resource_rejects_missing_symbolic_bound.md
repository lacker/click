# composite resource rejects missing symbolic bound

This checks that a composite resource fact still needs enough scalar
bounds to prove that each memory read is covered by contained write permission.

```click
resource indexed_zero(p: int32*, k: int32, n: int32) {
    contains write(p[0..n]);
    fact 0 <= k and p[k] == 0;
}
```

```expect
fail: resource `indexed_zero` fact reads `p[k]` without a covering contained `write(...)` resource
note: contained resource coverage considered:
  - `write(p[0..n])` has the right base, but the available scalar facts do not prove `0` <= `k` < `n`
note: scalar fact assumptions available: 0 <= k
```
