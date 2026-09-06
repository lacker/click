# algebraic let bindings reject mismatched annotations

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

spec enum Either<L, R> {
    Left(L),
    Right(R),
}

function rejected(value: int32) -> Maybe<int32> {
    let m: Maybe<int32> = Either<int32, int32>::Left(value);
    m
}
```

```expect
fail: let binding `m` expects Maybe<int32>, got Either<int32, int32>
```
