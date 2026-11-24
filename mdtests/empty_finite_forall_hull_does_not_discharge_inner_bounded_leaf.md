# An empty outer range does not discharge a leaf bounded only by the inner binder

The outer binder `k` has an empty range, so the chain has zero instances. The
second leaf is guarded only by `j`, whose range `0 <= j < 2` is not empty, so
it must be checked at each `j`, where `x == 7` is false at `x == 1`.

```click
theorem q(x: int32) {
    requires x > 0;
    ensures forall (k: int32) {
        forall (j: int32) {
            (5 <= k and k < 3 implies k == 1) and (0 <= j and j < 2 implies x == 7)
        }
    } by { close(); }
}
```

```expect
fail: could not establish `forall (k: int32)
```
