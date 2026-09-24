# instantiate a universal fact inside a pure theorem

Pure theorem proofs may specialize a universally quantified requirement with
the same checked rule used by fixed-state proofs.

```click
theorem bounded_value(value: int32) {
    requires forall (k: int32) {
        0 <= k and k < 3 implies k <= value
    };

    ensures 2 <= value by {
        instantiate(forall (k: int32) {
            0 <= k and k < 3 implies k <= value
        }, 2) using {}
        assumption();
    }
}

theorem instantiate_bound(x: int32, limit: int32, upper: int32) {
    requires forall (k: int32) {
        0 <= k and k < limit implies k <= upper
    };
    requires 0 <= x;
    requires x < limit;
    ensures x <= upper by {
        instantiate(forall (k: int32) {
            0 <= k and k < limit implies k <= upper
        }, x) using { 0 <= x; x < limit; }
        assumption();
    }
}

theorem instantiate_bound_caller(x: int32, limit: int32, upper: int32) {
    requires forall (k: int32) {
        0 <= k and k < limit implies k <= upper
    };
    requires 0 <= x;
    requires x < limit;
    ensures x <= upper by { apply(instantiate_bound(x, limit, upper)); }
}

```

```expect
pass
```
