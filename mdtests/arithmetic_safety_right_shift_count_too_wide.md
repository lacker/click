# Shifting right by 26 can still leave a 32-bit count of 32

```click quick-solve
theorem too_wide(d: uint32) {
    ensures d >> 26u32 < 32u32 by {
        close();
    }
}
```

```expect
fail: could not establish
```
