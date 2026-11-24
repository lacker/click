# OR with zero cannot establish a nonzero divisor

```click quick-solve
theorem no_set_bit(d: uint32) {
    ensures (d | 0u32) != 0u32 by {
        close();
    }
}
```

```expect
fail: could not establish
```
