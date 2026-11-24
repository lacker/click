# structural induction requires every constructor

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

theorem rejected(xs: TestList<int32>) {
    ensures xs == xs by {
        let ih = induct(xs);
        match xs {
            TestList::Nil => {
                close();
            }
        }
    }
}
```

```expect
fail: match must cover every constructor exactly once
```
