# A uint64 universal is not instantiated at an int32

The argument of `instantiate` has the binder's type. A signed 32-bit value
is not a `uint64`, and no conversion is supplied: `index` could be negative,
where the unsigned reading is a different number. The step is refused.

`instantiate_a_universal_over_uint64.md` passes a `uint64`.

```click
theorem below_ten(length: uint64, index: int32) {
    requires forall (k: uint64) { k < length implies k < 10u64 };

    ensures index < 10 by {
        instantiate(forall (k: uint64) { k < length implies k < 10u64 }, index);
        close();
    }
}
```

```expect
fail: `instantiate` argument did not evaluate to uint64
```
