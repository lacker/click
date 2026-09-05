# sequence membership requires matching element types

The left operand of `in` must have the sequence's element type. Membership
does not apply C's arithmetic conversions across the specification boundary.

```click
theorem mismatched_membership(value: int32) {
    ensures value in [0u8] by simp;
}
```

```expect
fail: membership element type does not match sequence element type
```
