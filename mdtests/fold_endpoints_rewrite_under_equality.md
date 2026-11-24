# Fold endpoint equality still requires defined endpoints

The first theorem compares folds under an explicit endpoint equality. The
second attempts to use `(hi - 1) + 1 == hi` for every `int32` value. Its
intermediate subtraction overflows at `INT32_MIN`, so the unchanged second
claim must now be rejected rather than silently guarded.

```click
theorem fold_endpoints_equal_from_an_equality(lo: int32, a: int32, b: int32) {
    requires a == b;
    ensures (lo..a).fold(0, |acc, k| { acc + to_integer(k) }) ==
        (lo..b).fold(0, |acc, k| { acc + to_integer(k) }) by {
        close();
    }
}

theorem fold_endpoint_predecessor_successor(lo: int32, hi: int32) {
    ensures (lo..((hi - 1) + 1)).fold(0, |acc, k| { acc + to_integer(k) }) ==
        (lo..hi).fold(0, |acc, k| { acc + to_integer(k) }) by {
        close();
    }
}
```

```expect
fail: not established: `hi - 1`
```
