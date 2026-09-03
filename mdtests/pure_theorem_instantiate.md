# instantiate a universal fact inside a pure theorem

Pure theorem proofs may specialize a universally quantified requirement with
the same checked rule used by fixed-state proofs.

```click
theorem bounded_value(value: int32) {
    requires bounded: forall (k: int32) {
        0 <= k and k < 3 implies k <= value
    };

    ensures 2 <= value by {
        instantiate(forall (k: int32) {
            0 <= k and k < 3 implies k <= value
        }, 2) using {}
        assumption();
    }
}
```

```expect
pass
```
