# Solve can weaken a bound on the same quotient

```click quick-solve
theorem probe(y: float) {
    requires float32_from_bits(0x3f800000) / y <= float32_from_bits(0x3f800000);
    ensures float32_from_bits(0x3f800000) / y < float32_from_bits(0x4f000000) by { close(); }
}
```

```expect
pass
```
