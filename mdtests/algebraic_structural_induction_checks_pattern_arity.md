# structural induction patterns bind every constructor field

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
            List::Cons(tail) => {
                simp();
            }
        }
    }
}
```

```expect
fail: pattern `List::Cons` expects 2 binding(s), got 1
```
