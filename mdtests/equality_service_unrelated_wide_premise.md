# An unrelated full-width equality does not obscure an atomic order fact

The full-width premise belongs to a different equality component. Matching the
int32 order uses only its selected scalar spellings.

```click quick-solve
theorem selected_order(x: int32, y: int32, z: int32, spare: uint64, other: uint64) {
    requires spare == other;
    requires x == y;
    requires y < z;
    ensures x < z by close();
}
```

```expect
pass
```
