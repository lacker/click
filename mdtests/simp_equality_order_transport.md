# simp transports equalities through integer bounds

`simp` deterministically rewrites order goals through known equalities,
normalizes discrete integer bounds, and evaluates equality-linked arithmetic.

```click
theorem rewrites_discrete_bound(length: int32, owner_length: int32) {
    requires 2 <= length;
    requires owner_length == length;

    ensures 1 < owner_length by simp;
}

theorem evaluates_equality_arithmetic(old_split: int32, split: int32) {
    requires old_split == 1;
    requires split == old_split + 1;

    ensures 1 < split by simp;
}
```

```expect
pass
```
