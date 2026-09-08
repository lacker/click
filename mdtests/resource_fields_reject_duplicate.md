# Resource fields have distinct names

```click
resource cell(p: int32*) {
    field model: List<int32>;
    field model: int32;
    owns p[0..1];
}
```

```expect
fail: resource `cell` field `model` duplicates a field or parameter name
```
