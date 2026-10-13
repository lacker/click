# A range `.all` with `size_t` bounds ranges over `size_t` indices

`(0..n).all(...)` with a `uint64` bound quantifies over `uint64` indices, as a
range fold with such a bound does, so it holds at an index past `2^32`. With a
32-bit binder it would say nothing about that index.

```click
theorem far_index(a: uint8[], n: uint64) {
    requires (0..n).all(|k| { a[k] == 0u8 });
    requires 4294967296u64 < n;
    ensures a[4294967296u64] == 0u8 by {
        instantiate((0..n).all(|k| { a[k] == 0u8 }), 4294967296u64) using {
            0u64 <= 4294967296u64;
            4294967296u64 < n;
        }
        assumption();
    }
}

theorem far_witness(a: uint8[], n: uint64) {
    requires 4294967296u64 < n;
    requires a[4294967296u64] == 7u8;
    ensures (0u64..n).any(|k| { a[k] == 7u8 }) by {
        witness { k: 4294967296u64 };
        simp();
    }
}
```

```expect
pass
```
