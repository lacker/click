# algebraic constructors check field types

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

theorem rejected(value: int32*) {
    ensures Maybe<int32>::Some(value) == Maybe<int32>::None by simp;
}
```

```expect
fail: constructor `Maybe::Some` argument 0 expects int32, got int32*
```
