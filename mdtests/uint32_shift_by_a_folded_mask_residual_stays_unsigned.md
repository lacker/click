# A residual unsigned shift keeps its result's type

The shifted bits are known but y is arbitrary, so normalization must refuse.
The residual reports the actual unsigned value instead of a negative int32.

```click
theorem cast_shift(x: uint64, y: uint32) {
    requires x == 1753877967969059832u64;
    ensures (182457789u32 << ((0u32 - (uint32)(x >> 59u64)) & 31u32)) == y by {
        rewrite(x == 1753877967969059832u64);
        normalize();
    }
}
```

```expect
fail: goal: 2684354560u32 == y
```
