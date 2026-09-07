# recursive algebraic datatype declarations require a finite constructor

```click
spec enum First {
    Next(Second),
}

spec enum Second {
    Next(First),
}
```

```expect
fail: recursive algebraic datatype `First` has no finite constructor value
```
