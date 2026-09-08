# A 64-bit rewrite still needs its exact equality premise

```click
theorem missing_equality(x: uint64, y: uint64) {
    ensures x + 3u64 == y + 3u64 by {
        rewrite(x == y);
        simp();
    }
}
```

```expect
fail: exact available fact
```
