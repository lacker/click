# Float narrowing can round up to the strict endpoint

```click quick-solve
theorem narrowing_can_round(x: double) {
    requires x <= float64_from_bits(0x3fefffffffffffff);
    ensures x as float < float32_from_bits(0x3f800000) by {
        close();
    }
}
```

```expect
fail: could not establish
```
