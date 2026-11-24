# A fold guard may be an Integer observation

Under Integer specification arithmetic a comparison that does arithmetic compares
exact Integers, so `n - k < 18446744073709551615u64` is Integer subtraction
and does not state the `uint64` guard the append law needs for the endpoint
`n - k`. The guard over that machine value is written as an Integer
observation, `to_integer(n - k) < 18446744073709551615`, which holds exactly
when the native comparison does. `unfold` reads a listed observation as that
native guard.

```click quick-solve

function total(lo: uint64, hi: uint64) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

theorem step(n: uint64, k: uint64) {
    requires 0 <= to_integer(n - k);
    requires to_integer(n - k) < 18446744073709551615;
    ensures total(0u64, (n - k) + 1u64) == total(0u64, n - k) + to_integer(n - k) by {
        unfold(total(0u64, (n - k) + 1u64));
        close();
    }
}
```

```expect
pass
```
