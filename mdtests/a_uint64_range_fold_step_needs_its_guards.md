# A uint64 range fold step needs its guards

The append law needs `lo <= hi` and `hi` below the largest `uint64`, where
`hi + 1u64` does not wrap. Ordinary `unfold` obligations must not silently
supply the missing upper bound.

```click
function total(lo: uint64, hi: uint64) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

theorem step(lo: uint64, hi: uint64) {
    requires lo <= hi;
    ensures total(lo, hi + 1u64) == total(lo, hi) + to_integer(hi) by {
        unfold(total(lo, hi + 1u64));
        close();
    }
}
```

```expect
fail: `unfold` has an unproved range-fold guard
```
