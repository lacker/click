# The high bit proves a 64-bit OR is nonzero

```click quick-solve
theorem set_high_bit(d: uint64) {
    ensures 0u64 != (9223372036854775808u64 | d) by {
        close();
    }
}
```

```expect
pass
```
