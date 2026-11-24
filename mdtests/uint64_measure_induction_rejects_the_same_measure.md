# A uint64 induction call must decrease

```click
theorem same_measure(n: uint64) {
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
