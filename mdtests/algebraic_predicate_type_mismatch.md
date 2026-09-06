# algebraic predicate arguments reject mismatched types

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

predicate has_int(value: Maybe<int32>) {
    value == value
}

theorem mismatched(value: Maybe<uint32>) {
    ensures has_int(value) by simp;
}
```

```expect
fail: predicate `has_int` argument 0 expects Maybe<int32>, got Maybe<uint32>
```
