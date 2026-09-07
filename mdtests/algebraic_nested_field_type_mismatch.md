# nested algebraic fields reject the wrong datatype

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

spec enum Either<L, R> {
    Left(L),
    Right(R),
}

spec enum Envelope<T> {
    Present(Maybe<T>),
}

function rejected(value: int32) -> Envelope<int32> {
    Envelope<int32>::Present(Either<int32, int32>::Left(value))
}
```

```expect
fail: constructor `Envelope::Present` argument 0 expects Maybe<int32>, got Either<int32, int32>
```
