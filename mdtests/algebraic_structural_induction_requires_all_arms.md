# structural induction requires every constructor

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
        }
    }
}
```

```expect
fail: structural induction is missing arm(s): Cons
```
