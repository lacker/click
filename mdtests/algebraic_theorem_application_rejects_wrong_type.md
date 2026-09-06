# algebraic theorem arguments retain their declared type

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

spec enum Either<L, R> {
    Left(L),
    Right(R),
}

theorem maybe_reflexive(m: Maybe<int32>) {
    ensures m == m by simp;
}

theorem rejected(value: int32) {
    ensures value == value by {
        apply(maybe_reflexive(Either<int32, int32>::Left(value)));
    }
}
```

```expect
fail: theorem `maybe_reflexive` parameter `m` expects algebraic type `Maybe`, got `Either`
```
