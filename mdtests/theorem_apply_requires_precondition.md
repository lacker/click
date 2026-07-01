# theorem application requires theorem preconditions

This checks that `apply(...)` rejects theorem applications whose requirements
are not available at the proof site.

```click
theorem positive_is_nonnegative(x: int32) {
    requires x > 0;

    ensures x >= 0 by auto;
}

theorem bad_apply(y: int32) {
    ensures y >= 0 by {
        apply(positive_is_nonnegative(y));
        simp();
    }
}
```

```expect
fail: could not prove requirement for theorem `positive_is_nonnegative`
```
