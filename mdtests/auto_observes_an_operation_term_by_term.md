# `auto` observes a machine operation term by term

A goal over `to_integer(a + b)` needs `to_integer(a + b) == to_integer(a) +
to_integer(b)`. For a signed operation `auto` proves it defined first and
applies `int32_add_to_integer`; for a `uint64` one it proves the sum does not
wrap and applies `uint64_add_to_integer`.

```click
theorem signed_observation(total: int32, b: int32) {
    requires 0 <= total;
    requires total <= 255000;
    requires 0 <= b;
    requires b <= 255;
    ensures to_integer(total + b) <= 255255 by {
        have to_integer(total + b) <= 255255 by auto;
        assumption();
    }
}

theorem unsigned_observation(i: uint64, n: uint64) {
    requires i < n;
    requires n <= 1000u64;
    ensures to_integer(i + 1u64) <= 1000 by {
        have to_integer(i + 1u64) <= 1000 by auto;
        assumption();
    }
}
```

```expect
pass
```
