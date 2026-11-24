# A literal constructor field keeps its value

A literal constructor argument is a value of its field's type, so
`Seq<int64>::Cons(3, ...)` is not `same(2)`, and the claim that it is
remains refused.

```click quick-solve
spec enum Seq<T> {
    Nil,
    Cons(T, Seq<T>),
}

function same(x: int64) -> Seq<int64> {
    Seq::Cons(x, Seq::Nil)
}

theorem wrong_literal() {
    ensures same(2) == Seq<int64>::Cons(3, Seq<int64>::Nil) by {
        unfold(same(2));
        close();
    }
}
```

```expect
fail: could not establish
```
