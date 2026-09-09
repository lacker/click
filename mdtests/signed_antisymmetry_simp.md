# Signed order antisymmetry emits a checkable equality certificate

```click
theorem bounded_equal(i: int32) {
    requires 0 <= i;
    requires i <= 0;
    ensures i == 0 by simp;
}
```

```expect
pass
```
