# Mathematical subtraction cannot hide unsigned underflow

For `n = 0` and `r = 1`, the Integer inequality `n - r < n` is true,
but its uint64 argument wraps to `UINT64_MAX`. The selected mathematical
bound cannot discharge the instantiated machine guard without its range fact.

```click
theorem wrapping_guard(n: uint64, r: uint64) {
    requires n == 0u64 and r == 1u64;
    requires forall (k: uint64) { k < n implies k == 0u64 };
    ensures true by {
        have n - r < n;
        have to_integer(n - r) < to_integer(n);
        instantiate(forall (k: uint64) { k < n implies k == 0u64 }, n - r);
        close();
    }
}
```

```expect
fail: could not establish
```
