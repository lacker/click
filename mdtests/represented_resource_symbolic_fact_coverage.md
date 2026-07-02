# represented resource symbolic fact coverage

This checks that a represented resource fact can justify an indexed
memory read using scalar bounds from the fact.

```click
affine resource indexed_zero(p: int32*, k: int32, n: int32) {
    contains write(p[0..n]);
    fact 0 <= k and k < n and p[k] == 0;
}
```

```expect
pass
```
