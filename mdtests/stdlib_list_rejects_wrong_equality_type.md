# Algebraic equality preserves type arguments

```click
theorem wrong_type(xs: List<int32>, ys: List<int32*>) {
    ensures (if xs == ys { 1 } else { 0 }) == 1 by simp;
}
```

```expect
fail: type
```
