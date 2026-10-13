# An unsigned shift evaluates a folded shift-count mask

Keep the original cast, unsigned subtraction, and mask in the shift count.
Rewriting x to its constant must leave a closed goal that normalize can prove.

```click
theorem cast_shift(x: uint64) {
    requires x == 1753877967969059832u64;
    ensures (182457789u32 << ((0u32 - (uint32)(x >> 59u64)) & 31u32)) == 2684354560u32 by {
        rewrite(x == 1753877967969059832u64);
        normalize();
    }
}
```

```expect
pass
```
