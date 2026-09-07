# generic calls reject conflicting inference

Every occurrence of one type parameter must infer the same concrete type.

```click
spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}

function append<T>(xs: List<T>, ys: List<T>) -> List<T> {
    xs
}

theorem conflicting_lists(
    ints: List<int32>,
    uints: List<uint32>
) {
    ensures append(ints, uints) == ints;
}
```

```expect
fail: type parameter `T` is both int32 and uint32
```
