# a larger induction argument is rejected

```click
theorem bad_larger(n: int32) {
    requires n >= 0;
    ensures n == n by {
        induct(n) as ih;
        apply(ih(n + 1));
        simp();
    }
}
```

```expect
fail: induction hypothesis `ih` could not prove premise `0 <= (n + 1)`
```
