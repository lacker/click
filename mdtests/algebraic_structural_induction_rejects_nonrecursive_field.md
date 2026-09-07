# structural induction hypotheses apply only to recursive children

```click
spec enum TestList<T> {
    Nil,
    Cons(T, TestList<T>),
}

theorem rejected(xs: TestList<int32>) {
    ensures xs == xs by {
        induct(xs) as ih {
            TestList::Nil => {
                simp();
            }
            TestList::Cons(head, tail) => {
                apply(ih(head));
                simp();
            }
        }
    }
}
```

```expect
fail: structural induction hypothesis expects an immediate recursive field
```
