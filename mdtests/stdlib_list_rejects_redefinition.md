# The standard-library list cannot be redeclared

```click
spec enum List<T> {
    Empty,
}
```

```expect
fail: duplicate algebraic datatype definition `List`
```
