# an induction hypothesis requires a strictly smaller argument

```click
theorem bad_same(n: int32) {
    requires n >= 0;
    ensures n == n by {
        induct(n) as ih;
        apply(ih(n));
        simp();
    }
}
```

```expect
fail: induction hypothesis `ih` could not prove premise `n < n`
```
