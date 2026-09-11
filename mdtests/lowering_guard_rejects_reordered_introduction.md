# A citation before its introduction is rejected

The companion of `lowering_guard_before_written_implication`. After the binder
and the definedness guard the written antecedent is still the goal's
implication, not a fact, so extracting one of its conjuncts before the third
`intro` has nothing to extract. Reordering the two introductions relative to
the citation must fail rather than quietly succeed against the guard.

```click
theorem guarded_universal_reordered() {
    ensures forall (k: int32) {
        k + 1 > 0 and k >= 0 implies k >= 0
    } by {
        intro();
        intro();
        extract(k >= 0);
        intro();
        assumption();
    }
}
```

```expect
fail: `extract`
```
