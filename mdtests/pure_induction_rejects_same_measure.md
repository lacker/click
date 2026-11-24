# an induction hypothesis requires a strictly smaller argument

```click
theorem bad_same(n: int32) {
    requires n >= 0;
    ensures n == n by {
        let ih = induct(n);
        apply(ih(n));
        close();
    }
}
```

```expect
fail: induction hypothesis `ih` found no available fact for premise `n < n`
```
