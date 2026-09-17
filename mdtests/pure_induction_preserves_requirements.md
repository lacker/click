# the induction hypothesis retains theorem requirements

```click
theorem restricted(n: int32) {
    requires n >= 5;
    ensures n == n by {
        induct(n) as ih;
        apply(ih(n - 1));
        simp();
    }
}
```

```expect
fail: induction hypothesis `ih` could not prove premise `(n - 1) >= 5`
```
