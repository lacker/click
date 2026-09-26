# Every `using` list accepts an equality in either orientation

`mdtests/using_premise_either_orientation.md` pins fixed-state `apply using`.
The mirrored spelling of a held equality is one fact, and every `using` list
now asks one availability rule for it, beside the rule for a premise that
holds without facts: a pure theorem's `apply using` and `instantiate using`
below each list `y == x` while the proof holds `x == y`.
This used to be a local rule in the two fixed-state checkers only.

```click
theorem value_symmetric(a: int32, b: int32) {
    requires a == b;
    ensures b == a by { simp(); }
}

theorem pure_apply_mirrored(x: int32, y: int32) {
    requires x == y;
    ensures x == y by {
        apply(value_symmetric(y, x)) using { y == x; }
        assumption();
    }
}

theorem instantiate_mirrored(x: int32, y: int32) {
    requires x == y;
    requires forall (k: int32) { k == x implies 0 <= 0 };
    ensures 0 <= 0 by {
        instantiate(forall (k: int32) { k == x implies 0 <= 0 }, y) using { y == x; }
        assumption();
    }
}
```

```expect
pass
```
