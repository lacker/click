# theorem application requires an exact premise

`x > 0` implies `x >= 0`, but `apply` is a simple tactic and does not search
for that derivation. The required premise must first be present as an exact
pure fact.

```click
theorem needs_nonnegative(x: int32) {
    requires x >= 0;

    ensures x >= 0 by {
        assumption();
    }
}

theorem positive_is_not_an_exact_premise(x: int32) {
    requires x > 0;

    ensures x >= 0 by {
        apply(needs_nonnegative(x));
        assumption();
    }
}
```

```expect
fail: required exact fact
```
