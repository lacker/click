# algebraic matches must be exhaustive

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

theorem rejected(value: int32) {
    ensures match Maybe<int32>::Some(value) {
        Maybe::Some(inner) => inner,
    } == value by simp;
}
```

```expect
fail: match for `Maybe` is not exhaustive; missing None
```
