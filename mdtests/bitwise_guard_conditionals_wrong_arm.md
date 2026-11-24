# A false bitwise guard cannot select the true arm

```click
theorem wrong_bitwise_guard(z: uint64, y: uint64) {
    requires not ((z & 7u64) < y);
    ensures (if (z & 7u64) < y { 7u64 } else { 9u64 }) == 7u64 by {
        close();
    }
}
```

```expect
fail: could not establish `(if (z & 7u64) as uint64 < y { 7u64 } else { 9u64 }) == 7u64`
```
