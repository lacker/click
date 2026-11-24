# the induction hypothesis retains theorem requirements

```click
theorem restricted(n: int32) {
    requires n >= 5;
    ensures n == n by {
        let ih = induct(n);
        have 0 <= to_integer(n - 1);
        have to_integer(n - 1) < to_integer(n);
        apply(ih(n - 1));
        close();
    }
}
```

```expect
fail: induction hypothesis `ih` found no available fact for premise `to_integer(((n - 1) as int32)) >= 5`
```
