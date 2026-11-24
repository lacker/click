# An unsigned predecessor at zero is larger

```click
theorem wrapped_predecessor(n: uint64) {
    requires n == 0u64;
    ensures n == n by {
        let ih = induct(n);
        apply(ih(n - 1u64));
        close();
    }
}
```

```expect
fail: induction hypothesis `ih` found no available fact for premise
```
