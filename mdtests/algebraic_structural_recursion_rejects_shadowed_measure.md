# a shadowed measure name is not the original recursive value

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

function shadowed(xs: TestList<int32>, other: TestList<int32>) -> int32
    decreases xs
{
    match other {
        TestList::Nil => 0,
        TestList::Cons(head, xs) => match xs {
            TestList::Nil => 0,
            TestList::Cons(next, tail) => shadowed(tail, other),
        },
    }
}
```

```expect
fail: recursive call `shadowed` -> `shadowed` must pass a recursive field structurally below `xs` as its decreases argument
```
