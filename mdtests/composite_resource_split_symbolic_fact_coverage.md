# composite resource split symbolic fact coverage

This checks that scalar bounds declared as separate composite-resource facts
can jointly justify a later indexed memory fact.

```click
resource indexed_zero(p: int32*, k: int32, n: int32) {
    owns p[0..n];
    fact 0 <= k;
    fact k < n;
    fact p[k] == 0;
}
```

```expect
pass
```
