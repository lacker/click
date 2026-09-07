# recursive algebraic datatypes preserve their parameters

The first recursive slice is regular: crossing a recursive cycle cannot
change the enclosing datatype's type arguments.

```click
spec enum Maybe<T> {
    None,
    Some(T),
}

spec enum Bad<T> {
    Stop,
    More(Bad<Maybe<T>>),
}
```

```expect
fail: recursive algebraic datatype occurrence in variant `Bad::More` must preserve type parameters exactly
```
