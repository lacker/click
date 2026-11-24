# theorem application requires theorem preconditions

This checks that `apply(...)` rejects theorem applications whose
premise obligations cannot be proved at the application site.

```click
theorem positive_is_nonnegative(x: int32) {
    requires x > 0;

    ensures x >= 0;
}

theorem bad_apply(y: int32) {
    ensures y >= 0 by {
        apply(positive_is_nonnegative(y));
        close();
    }
}
```

```expect
fail: theorem `positive_is_nonnegative` has an unproved obligation
```
