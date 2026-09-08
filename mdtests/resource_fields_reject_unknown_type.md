# Resource field types are checked even in unused declarations

```click
resource cell(p: int32*) {
    field model: Missing;
    owns p[0..1];
}
```

```expect
fail: unknown algebraic datatype `Missing` in resource `cell` field `model`
```
