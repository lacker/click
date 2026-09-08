# Quantities do not apply to field-bearing resources

Even a quantity of one must not route through the counted-resource machinery.

```click
resource cell(p: int32*) {
    field model: List<int32>;
    owns p[0..1];
}

int32 read_cell(int32* p) {
    consumes 1 of cell(p);
}
```

```expect
fail: resource `cell` has fields and is not countable
```
