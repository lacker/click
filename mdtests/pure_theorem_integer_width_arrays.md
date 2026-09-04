# Pure theorem setup preserves wide array parameter types

Pure theorem parameter setup must represent fixed-width integer arrays as
typed pointers. It must not ask an array type for a pointee type or silently
fall back to a four-byte element width.

```click
theorem int64_array_identity(values: int64[]) {
    ensures values[0] == values[0] by {
        simp();
    }
}

theorem uint64_array_identity(values: uint64[]) {
    ensures values[0] == values[0] by {
        simp();
    }
}
```

```expect
pass
```
