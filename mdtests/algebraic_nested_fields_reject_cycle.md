# nested algebraic datatype declarations reject cycles

```click
spec enum First {
    Next(Second),
}

spec enum Second {
    Next(First),
}
```

```expect
fail: recursive algebraic datatype cycle `First -> Second -> First` is not supported in the nonrecursive slice
```
