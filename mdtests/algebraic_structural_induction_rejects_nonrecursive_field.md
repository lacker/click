# structural induction hypotheses apply only to recursive children

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
            TestList::Cons(head, tail) => {
                apply(ih(head));
                close();
            }
        }
    }
}
```

```expect
fail: structural induction hypothesis expects an immediate recursive field
```
