# represented resource symbolic invariant coverage

This checks that a represented resource invariant can justify an indexed
memory read using scalar bounds from the invariant.

```click
affine resource indexed_zero(p: int32*, k: int32, n: int32) {
    contains write(p[0..n]);
    invariant 0 <= k and k < n and p[k] == 0;
}
```

```expect
pass
```
