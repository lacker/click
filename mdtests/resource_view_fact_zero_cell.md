# A current viewed cell covers a zero-valued fact read

Stable read authority is enough to validate a resource fact even when the
cell's value is zero.

```click
resource viewed_zero_cell(p: int32*) {
    views p[0..1];
    fact p[0] == 0;
}
```

```expect
pass
```
