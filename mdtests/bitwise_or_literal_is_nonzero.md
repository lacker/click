# A nonzero OR literal proves a 32-bit word is nonzero

```click quick-solve
theorem set_bit32(d: uint32) {
    ensures (d | 1u32) != 0u32 by {
        close();
    }
}
```

```expect
pass
```
