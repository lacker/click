# Plain normalization stays context-free

```click
theorem plain(xs: List<int32>, ys: List<int32>) {
    requires xs == ys;
    ensures (if xs == ys { 1 } else { 0 }) == 1 by {
        normalize();
    }
}
```

```expect
fail: normalize
```
