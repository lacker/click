# Signed allocation bounds establish unsigned byte-count bounds

Unsigned order lowers to signed order after flipping the sign bit. Explicit
signed bounds must suffice to check the resulting byte-count obligation, without
search or an extra unsigned assumption.

```click
theorem allocation_range_fits(length: int32) {
    requires 0 <= length;
    requires length <= 536870911;
    ensures ((uint32)length) <= 1073741823u32 by {
        arithmetic() using {
            0 <= length;
            length <= 536870911;
        }
    }
}
```

```expect
pass
```
