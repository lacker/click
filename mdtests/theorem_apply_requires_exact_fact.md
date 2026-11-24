# A theorem application cannot obtain a bound absent from the proof

```click
theorem needs_nonnegative(x: int32) {
    requires x >= 0;

    ensures x >= 0 by {
        close();
    }
}

theorem positive_is_not_an_exact_premise(x: int32) {
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
