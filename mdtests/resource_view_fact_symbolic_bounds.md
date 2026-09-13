# A current view covers a symbolically bounded fact read

The existing scalar-bound analysis also applies to read authority supplied by
a current view.

```click
resource viewed_symbolic_cell(p: int32*, k: int32, n: int32) {
    views p[0..n];
    fact 0 <= k and k < n and p[k] == 0;
}
```

```expect
pass
```
