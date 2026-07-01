# represented resource rejects missing symbolic bound

This checks that a represented resource invariant still needs enough scalar
bounds to prove that each memory read is covered by contained write permission.

```click
affine resource indexed_zero(p: int32*, k: int32, n: int32) {
    contains write(p[0..n]);
    invariant 0 <= k and p[k] == 0;
}
```

```expect
fail: resource `indexed_zero` invariant reads `p[k]` without a covering contained `write(...)` resource
```
