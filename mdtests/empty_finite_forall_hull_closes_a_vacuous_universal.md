# An empty finite universal range closes a universal whose every leaf it guards

Both leaves are guarded by a range of `k` that no integer satisfies, so the
universal is vacuously true and checking zero instances is exactly its
evidence. This is the positive twin of
`mdtests/empty_finite_forall_hull_does_not_discharge_unquantified_leaf.md`.

```click quick-solve
theorem q(x: int32) {
    requires x > 0;
    ensures forall (k: int32) {
        (5 <= k and k < 3 implies k == 1) and (7 <= k and k < 6 implies x == 7)
    } by { close(); }
}
```

```expect
pass
```
