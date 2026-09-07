# fields of an unrelated value do not justify recursion

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

function unrelated(xs: TestList<int32>, other: TestList<int32>) -> int32
    decreases xs
{
    match other {
        TestList::Nil => 0,
        TestList::Cons(head, tail) => unrelated(tail, other),
    }
}
```

```expect
fail: recursive call `unrelated` -> `unrelated` must pass a recursive field structurally below `xs` as its decreases argument
```
