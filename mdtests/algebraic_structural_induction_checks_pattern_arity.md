# structural induction patterns bind every constructor field

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
            TestList::Cons(tail) => {
                simp();
            }
        }
    }
}
```

```expect
fail: pattern `TestList::Cons` expects 2 binding(s), got 1
```
