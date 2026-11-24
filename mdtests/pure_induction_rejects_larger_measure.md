# a larger induction argument is rejected

The argument `n + 1` is defined here, so the premise the hypothesis cannot
prove is the decrease itself.

```click
theorem bad_larger(n: int32) {
    requires n >= 0;
    requires n <= 100;
    ensures n == n by {
        let ih = induct(n);
        have 0 <= to_integer(n + 1);
        apply(ih(n + 1));
        close();
    }
}
```

```expect
fail: induction hypothesis `ih` found no available fact for premise `to_integer(((n + 1) as int32)) < to_integer((n as int32))`
```
