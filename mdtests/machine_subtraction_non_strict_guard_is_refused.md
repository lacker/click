# A non-strict subtraction bound cannot prove a strict guard

```click
theorem non_strict_guard(n: uint64, r: uint64) {
    requires r == 0u64 and n != 0u64;
    requires forall (k: uint64) { k < n implies k == 0u64 };
    ensures true by {
        have n - r <= n;
        have to_integer(n - r) < to_integer(n);
        instantiate(forall (k: uint64) { k < n implies k == 0u64 }, n - r);
        close();
    }
}
```

```expect
fail: could not establish
```
