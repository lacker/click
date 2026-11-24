# A selected undefined shift still owes its domain

```click
theorem selected_bitwise_shift(z: uint64, y: uint64) {
    requires (z & 7u64) < y;
    ensures (if (z & 7u64) < y { 1u64 << 64u64 } else { z }) == z by {
        close();
    }
}
```

```expect
fail: it denotes a value only where
```
