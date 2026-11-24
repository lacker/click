# Applying a named theorem exposes its premises as obligations

```click
theorem nonnegative(n: Integer) {
    requires n >= 0;
    ensures n >= 0 by close();
}
theorem positive(n: Integer) {
    ensures n >= 0 by {
        apply(nonnegative(n));
    }
}
```

```expect
fail: has an unproved obligation
```
