# A selected invalid shift remains undefined under a reflexive guard

```click
theorem selected_reflexive_shift(y: uint64) {
    ensures (if y == y { 1u64 << 64u64 } else { 3u64 }) == 3u64 by { close(); }
}
```

```expect
fail: it denotes a value only where
```
