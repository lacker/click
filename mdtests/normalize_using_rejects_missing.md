# Cited evidence must exist

```click
theorem missing(xs: List<int32>, ys: List<int32>) {
    ensures (if xs == ys { 1 } else { 0 }) == 1 by {
        normalize() using { xs == ys; }
    }
}
```

```expect
fail: not exactly available
```
