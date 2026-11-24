# Widening a non-strict bound cannot make it strict

```click quick-solve
theorem strict_bound(x: float) {
    requires x <= float32_from_bits(0x3f800000);
    ensures x as double < float64_from_bits(0x3ff0000000000000) by {
        close();
    }
}
```

```expect
fail: could not establish
```
