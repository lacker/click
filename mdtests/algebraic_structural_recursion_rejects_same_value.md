# algebraic recursion must use a strict structural subterm

```click
spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}

function stuck(xs: List<int32>) -> int32
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) => stuck(xs),
    }
}
```

```expect
fail: recursive call `stuck` -> `stuck` must pass a recursive field structurally below `xs` as its decreases argument
```
