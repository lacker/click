# fields of an unrelated value do not justify recursion

```click
spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}

function unrelated(xs: List<int32>, other: List<int32>) -> int32
    decreases xs
{
    match other {
        List::Nil => 0,
        List::Cons(head, tail) => unrelated(tail, other),
    }
}
```

```expect
fail: recursive call `unrelated` -> `unrelated` must pass a recursive field structurally below `xs` as its decreases argument
```
