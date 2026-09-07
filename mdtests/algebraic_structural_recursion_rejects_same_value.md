# algebraic recursion must use a strict structural subterm

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

function stuck(xs: TestList<int32>) -> int32
    decreases xs
{
    match xs {
        TestList::Nil => 0,
        TestList::Cons(head, tail) => stuck(xs),
    }
}
```

```expect
fail: recursive call `stuck` -> `stuck` must pass a recursive field structurally below `xs` as its decreases argument
```
