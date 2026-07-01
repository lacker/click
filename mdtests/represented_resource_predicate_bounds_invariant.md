# represented resource predicate bounds invariant

This checks that scalar bounds hidden behind a predicate can justify a
represented resource invariant memory read.

```click
predicate in_bounds(int32 k, int32 n) {
    0 <= k and k < n
}

affine resource indexed_zero(p: int32*, k: int32, n: int32) {
    contains write(p[0..n]);
    invariant in_bounds(k, n) and p[k] == 0;
}
```

```expect
pass
```
