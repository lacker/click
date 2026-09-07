# structural induction requires every constructor

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
        }
    }
}
```

```expect
fail: structural induction is missing arm(s): Cons
```
