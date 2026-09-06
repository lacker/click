# algebraic matches reject duplicate variants

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

theorem rejected(value: int32, fallback: int32) {
    ensures match Maybe<int32>::Some(value) {
        Maybe::None => fallback,
        Maybe::Some(first) => first,
        Maybe::Some(second) => second,
    } == value by simp;
}
```

```expect
fail: match for `Maybe` repeats variant `Some`
```
