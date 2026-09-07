# a shadowed measure name is not the original recursive value

```click
spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}

function shadowed(xs: List<int32>, other: List<int32>) -> int32
    decreases xs
{
    match other {
        List::Nil => 0,
        List::Cons(head, xs) => match xs {
            List::Nil => 0,
            List::Cons(next, tail) => shadowed(tail, other),
        },
    }
}
```

```expect
fail: recursive call `shadowed` -> `shadowed` must pass a recursive field structurally below `xs` as its decreases argument
```
