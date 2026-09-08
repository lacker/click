# Unlisted ambient conditions cannot select a branch

```click
theorem ambient(xs: List<int32>, ys: List<int32>, x: int32) {
    requires xs == ys;
    requires x == 0;
    ensures (if xs == ys { 1 } else { 0 }) == 1 by {
        normalize() using { x == 0; }
    }
}
```

```expect
fail: did not normalize
```
