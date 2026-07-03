# represented resource predicate bounds fact

This checks that scalar bounds hidden behind a predicate can justify a
represented resource fact memory read.

```click
predicate in_bounds(int32 k, int32 n) {
    0 <= k and k < n
}

resource indexed_zero(p: int32*, k: int32, n: int32) {
    contains write(p[0..n]);
    fact in_bounds(k, n) and p[k] == 0;
}
```

```expect
pass
```
