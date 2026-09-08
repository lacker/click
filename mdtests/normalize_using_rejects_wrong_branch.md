# A checked opposite condition does not establish the wrong branch

```click
theorem wrong(xs: List<int32>, ys: List<int32>) {
    requires not(xs == ys);
    ensures (if xs == ys { 1 } else { 0 }) == 1 by {
        normalize() using { not(xs == ys); }
    }
}
```

```expect
fail: did not normalize
```
