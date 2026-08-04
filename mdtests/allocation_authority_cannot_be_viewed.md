# allocation authority cannot be viewed

Allocation authority is an owned lifetime obligation, not a duplicable
observation.

```click
resource invalid_allocation_view(item: int32*, bytes: int32) {
    views allocation(item, bytes);
}
```

```expect
fail: allocation authority is owned and cannot be viewed or duplicated
```
