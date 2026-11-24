# An empty finite universal range does not discharge a leaf outside the binder

The first leaf's guard `5 <= k and k < 3` holds for no `k`, so the universal
has zero instances to check. The second leaf does not mention `k`: it is the
same proposition at every `k`, and `x > 0 implies x == 7` is false at
`x == 1`, so the universal is false and the empty range must not close it.

```click quick-solve
theorem q(x: int32) {
    requires x > 0;
    ensures forall (k: int32) {
        (5 <= k and k < 3 implies k == 1) and (x > 0 implies x == 7)
    } by { close(); }
}
```

```expect
fail: could not establish `forall (k: int32)
```
