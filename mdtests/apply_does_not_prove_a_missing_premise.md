# A theorem application reports a missing premise

```click
theorem needs_nonnegative(x: int32) {
    requires x >= 0;

    ensures x >= 0 by {
        close();
    }
}

theorem positive_premise(x: int32) {
    requires x < 0;

    ensures x >= 0 by {
        apply(needs_nonnegative(x));
        close();
    }
}
```

```expect
fail: theorem `needs_nonnegative` has an unproved obligation
```
