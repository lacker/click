# Applying a theorem over a byte range owes the range's span half

The caller has a readable range ending at `n` and needs a theorem over
`v[lo..k]`. With the lower bound on `k` absent, the call cannot establish
that range and its span conditions.

```click
theorem stated_byte_range_span_is_nonnegative(v: uint8[], lo: int32, hi: int32) {
    views v[lo..hi];
    requires defined(hi - lo);
    ensures 0 <= to_integer(hi - lo) by close();
}

theorem narrowed_byte_range_owes_its_span(v: uint8[], lo: int32, n: int32, k: int32) {
    views v[lo..n];
    requires k <= n;
    requires defined(k - lo);
    ensures 0 <= to_integer(k - lo) by {
        apply(stated_byte_range_span_is_nonnegative(v, lo, k));
    }
}
```

```expect
fail: has an unproved obligation
```
