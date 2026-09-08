# Explicit 64-bit equality rewriting

```click
theorem wide_rewrite(x: uint64, y: uint64) {
    requires x == y;
    ensures x + 3u64 == y + 3u64 by {
        rewrite(x == y);
        simp();
    }
}
theorem wide_rewrite_reverse(x: uint64, y: uint64) {
    requires x == y;
    ensures y * 3u64 == x * 3u64 by {
        rewrite(y == x);
        simp();
    }
}
```

```expect
pass
```
