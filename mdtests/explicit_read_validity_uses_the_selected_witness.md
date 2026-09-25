# Explicit validity belongs to the selected witness

Validity at index zero cannot establish validity at index one, even though
both logical reads have values. The written conjunction uses one witness.

```click
theorem wrong_cell(p: int32[]) {
    requires defined(p[0]);
    ensures exists (k: Integer) { k == 1 and defined(p[to_int32(k)]) } by {
        witness(k = 1);
        simp();
    }
}
```

```expect
fail: simp
```
