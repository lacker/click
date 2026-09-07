# generic calls reject conflicting inference

Every occurrence of one type parameter must infer the same concrete type.

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

function append<T>(xs: TestList<T>, ys: TestList<T>) -> TestList<T> {
    xs
}

theorem conflicting_lists(
    ints: TestList<int32>,
    uints: TestList<uint32>
) {
    ensures append(ints, uints) == ints;
}
```

```expect
fail: type parameter `T` is both int32 and uint32
```
