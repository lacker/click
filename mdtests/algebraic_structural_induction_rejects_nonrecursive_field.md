# structural induction hypotheses apply only to recursive children

```click
spec enum List<T> {
    Nil,
    Cons(T, List<T>),
}

theorem rejected(xs: List<int32>) {
    ensures xs == xs by {
        induct(xs) as ih {
            List::Nil => {
                simp();
            }
            List::Cons(head, tail) => {
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
