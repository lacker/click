# Field-bearing resources cannot be counted

```click
resource cell(p: int32*) {
    field model: List<int32>;
    owns p[0..1];
}

int32 read_cell(int32* p) {
    requires count(cell(p)) == 1;
}
```

```expect
fail: resource `cell` has fields and is not countable
```
