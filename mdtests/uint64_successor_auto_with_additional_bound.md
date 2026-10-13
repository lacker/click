# UInt64 successor arithmetic

```click
theorem successor_bound(length: uint64) {
    requires length < 18446744073709551615u64;
    requires length + 1u64 <= 9223372036854775807u64;
    ensures to_integer(length) + 1 <= 18446744073709551615 by {
        apply(uint64_less_than_to_integer(length, 18446744073709551615u64));
        have to_integer(length) + 1 <= 18446744073709551615 by auto;
        assumption();
    }
}
```

```expect
pass
```
